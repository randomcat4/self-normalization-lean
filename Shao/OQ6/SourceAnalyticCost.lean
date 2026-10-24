import Shao.OQ6.WeightedDeletionMoments
import Shao.OQ6.PartialObservationTilt
import Shao.OQ6.ActualQuadraticTiltMoments
import Shao.OQ6.ObservationProductTilt
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Exact original-length p37(1) analytic cost only. The probability engine
remains attributed to Shao--Zhou; envelope validity and all original roots remain open. -/

set_option autoImplicit false

namespace Shao.OQ6.SourceAnalyticCost

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem actual_quadratic_source_analytic_cost
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (h : Ω → Ω → ℝ)
    (hh : Measurable (fun z : Ω × Ω => h z.1 z.2))
    (hh2 : MemLp (fun z : Ω × Ω => h z.1 z.2) 2 (μ.prod μ))
    (hhsymm : ∀ o y, h o y = h y o)
    (hcenter : (∫ z : Ω × Ω, h z.1 z.2 ∂(μ.prod μ)) = 0)
    (hprojectionsecond :
      (∫ o, (∫ y, h o y ∂μ) ^ 2 ∂μ) = 1)
    (n : ℕ) (hn : 3 ≤ n)
    (x : ℝ) (hx : 1 ≤ x)
    (hwindow : x ≤ Real.sqrt (n : ℝ) /
      (2 * Real.exp (1 / 2 : ℝ)))
    (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    let C : ℝ := Real.exp (1 / 2 : ℝ)
    let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
    let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
    let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
    let s : ℝ := 1 + Real.sqrt v
    let a : ℝ := x / Real.sqrt (n : ℝ)
    let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
    let m : ℝ := ∫ o, Real.exp (φ o) ∂μ
    let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
    let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
    let Sminus : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j ∈ Finset.univ.erase i, φ (ξ j)
    let I : ℝ := m ^ n
    let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
    let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Real.exp (Sminus ξ i) / I
    let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      min |a * g (ξ i)| 1
    let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
      fun ξ j k => r (ξ j) (ξ k)
    let F : (Fin n → Ω) → ℝ := fun ξ =>
      Shao.OQ5.P35.unorderedPairSum (e ξ)
    let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Shao.OQ5.P35.unorderedPairSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
    let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
      Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
    let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
      Shao.OQ6.ResidualDeletion.rowSum
        (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
    let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
      ∑ j : Fin n, ψ ξ j ^ 2
    let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      ∑ j : Fin n, ψdel ξ i j ^ 2
    let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
      F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
    let A : (Fin n → Ω) → ℝ := fun ξ => |D₁ ξ|
    let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D₁del ξ i|
    let D₃ : (Fin n → Ω) → ℝ := fun ξ =>
      C₀ * (s * x / Real.sqrt (n : ℝ) +
        Λsq ξ / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
    let D₃del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      C₀ * (s * x / Real.sqrt (n : ℝ) +
        Λdelsq ξ i / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
    let fullTest : (Fin n → Ω) → ℝ := fun ξ => x * A ξ + x ^ 2 * D₃ ξ
    let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
      cap ξ i * (|A ξ - Adel ξ i| + x * |D₃ ξ - D₃del ξ i|)
    let sourceCost : ℝ :=
      ((∫ ξ, fullTest ξ * Real.exp (S ξ) ∂P₀) +
        ∑ i : Fin n,
          ∫ ξ, deletedTest ξ i * Real.exp (Sminus ξ i) ∂P₀) / I
    Integrable (fun ξ => fullTest ξ * Real.exp (S ξ)) P₀ ∧
      (∀ i : Fin n, Integrable
        (fun ξ => deletedTest ξ i * Real.exp (Sminus ξ i)) P₀) ∧
      sourceCost =
        x * (∫ ξ, A ξ ∂Pₐ) + x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) +
          ∑ i : Fin n,
            ∫ ξ, R ξ i * deletedTest ξ i ∂P₀ ∧
      sourceCost ≤
        64 * C ^ 4 * (1 + C₀) * s * (1 + x) ^ 3 / Real.sqrt (n : ℝ) := by
  classical
  dsimp only
  let C : ℝ := Real.exp (1 / 2 : ℝ)
  let g : Ω → ℝ := fun o => ∫ y, h o y ∂μ
  let r : Ω → Ω → ℝ := fun o y => h o y - g o - g y
  let v : ℝ := ∫ z : Ω × Ω, r z.1 z.2 ^ 2 ∂(μ.prod μ)
  let s : ℝ := 1 + Real.sqrt v
  let a : ℝ := x / Real.sqrt (n : ℝ)
  let φ : Ω → ℝ := fun o => a * g o - (a * g o) ^ 2 / 2
  let m : ℝ := ∫ o, Real.exp (φ o) ∂μ
  let P₀ : Measure (Fin n → Ω) := Measure.pi (fun _ : Fin n => μ)
  let S : (Fin n → Ω) → ℝ := fun ξ => ∑ j : Fin n, φ (ξ j)
  let Sminus : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j ∈ Finset.univ.erase i, φ (ξ j)
  let I : ℝ := m ^ n
  let Pₐ : Measure (Fin n → Ω) := P₀.tilted S
  let R : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Real.exp (Sminus ξ i) / I
  let cap : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    min |a * g (ξ i)| 1
  let e : (Fin n → Ω) → Fin n → Fin n → ℝ :=
    fun ξ j k => r (ξ j) (ξ k)
  let F : (Fin n → Ω) → ℝ := fun ξ =>
    Shao.OQ5.P35.unorderedPairSum (e ξ)
  let Fdel : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Shao.OQ5.P35.unorderedPairSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i)
  let ψ : (Fin n → Ω) → Fin n → ℝ := fun ξ j =>
    Shao.OQ6.ResidualDeletion.rowSum (e ξ) j
  let ψdel : (Fin n → Ω) → Fin n → Fin n → ℝ := fun ξ i j =>
    Shao.OQ6.ResidualDeletion.rowSum
      (Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i) j
  let Λsq : (Fin n → Ω) → ℝ := fun ξ =>
    ∑ j : Fin n, ψ ξ j ^ 2
  let Λdelsq : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    ∑ j : Fin n, ψdel ξ i j ^ 2
  let D₁ : (Fin n → Ω) → ℝ := fun ξ =>
    F ξ / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let D₁del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    Fdel ξ i / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))
  let A : (Fin n → Ω) → ℝ := fun ξ => |D₁ ξ|
  let Adel : (Fin n → Ω) → Fin n → ℝ := fun ξ i => |D₁del ξ i|
  let D₃ : (Fin n → Ω) → ℝ := fun ξ =>
    C₀ * (s * x / Real.sqrt (n : ℝ) +
      Λsq ξ / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
  let D₃del : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    C₀ * (s * x / Real.sqrt (n : ℝ) +
      Λdelsq ξ i / (s * x * ((n : ℝ) ^ 2 * Real.sqrt (n : ℝ))))
  let fullTest : (Fin n → Ω) → ℝ := fun ξ => x * A ξ + x ^ 2 * D₃ ξ
  let deletedTest : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    cap ξ i * (|A ξ - Adel ξ i| + x * |D₃ ξ - D₃del ξ i|)
  let sourceCost : ℝ :=
    ((∫ ξ, fullTest ξ * Real.exp (S ξ) ∂P₀) +
      ∑ i : Fin n,
        ∫ ξ, deletedTest ξ i * Real.exp (Sminus ξ i) ∂P₀) / I
  let N : ℝ := (n : ℝ)
  let t : ℝ := Real.sqrt N
  let d : ℝ := t * (N - 1)
  let K : ℝ := N ^ 2 * t
  let k : ℝ := C₀ / (s * x * K)
  let b : ℝ := x * k
  let U : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    R ξ i * cap ξ i * |A ξ - Adel ξ i|
  let V : (Fin n → Ω) → Fin n → ℝ := fun ξ i =>
    R ξ i * cap ξ i * |Λsq ξ - Λdelsq ξ i|
  let T : ℝ := s * (1 + x) ^ 3 / t
  change Integrable (fun ξ => fullTest ξ * Real.exp (S ξ)) P₀ ∧
    (∀ i : Fin n, Integrable
      (fun ξ => deletedTest ξ i * Real.exp (Sminus ξ i)) P₀) ∧
    sourceCost = x * (∫ ξ, A ξ ∂Pₐ) + x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) +
      ∑ i : Fin n, ∫ ξ, R ξ i * deletedTest ξ i ∂P₀ ∧
    sourceCost ≤ 64 * C ^ 4 * (1 + C₀) * s * (1 + x) ^ 3 / t
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hxp : 0 < x := lt_of_lt_of_le (by norm_num) hx
  have hN3 : (3 : ℝ) ≤ N := by dsimp only [N]; exact_mod_cast hn
  have hNp : 0 < N := by linarith only [hN3]
  have hN0 : 0 ≤ N := hNp.le
  have htp : 0 < t := Real.sqrt_pos.mpr hNp
  have hdp : 0 < d := mul_pos htp (by linarith only [hN3])
  have hKp : 0 < K := mul_pos (sq_pos_of_pos hNp) htp
  have hC1 : 1 ≤ C := Real.one_le_exp (by norm_num)
  have hCpos : 0 < C := lt_of_lt_of_le (by norm_num) hC1
  have source := Shao.OQ6.ActualQuadraticTiltMoments.actual_quadratic_source_moments
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn x hx0 hwindow
  rcases source with
    ⟨hg, hg2, hgmean, hgsecond, hr, hr2, hrsymm, hrcan,
      hv, hs1, hvs, hw, hmlo, hmhi, hL, hL1, hLb, hLmass,
      hδint, hδbd, htilt, hρprob, hFullExp, hFullNorm, hFullPos,
      hFullPoint, hFullDensity, hFullProduct, hFullProb,
      hF2, hFsq, hRows, hΛ,
      hFid, hΛid, hFbin, hΛbin, hFpoly, hΛpoly, hFfinal, hΛfinal⟩
  change Measurable g at hg
  change Measurable (fun z : Ω × Ω => r z.1 z.2) at hr
  change 1 ≤ s at hs1
  change Integrable (fun ξ => Real.exp (S ξ)) P₀ at hFullExp
  change (∫ ξ, Real.exp (S ξ) ∂P₀) = I at hFullNorm
  change 0 < I at hFullPos
  change IsProbabilityMeasure Pₐ at hFullProb
  change MemLp F 2 Pₐ at hF2
  change Integrable Λsq Pₐ at hΛ
  change (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
    14 * C ^ 4 * s ^ 2 * N ^ 2 * (1 + x ^ 4) at hFfinal
  change (∫ ξ, Λsq ξ ∂Pₐ) ≤
    14 * C ^ 4 * s ^ 2 * N ^ 2 * (1 + x ^ 2) at hΛfinal
  letI : IsProbabilityMeasure Pₐ := hFullProb
  have hsp : 0 < s := lt_of_lt_of_le (by norm_num) hs1
  have hdenLp : 0 < s * x * K := mul_pos (mul_pos hsp hxp) hKp
  have hk0 : 0 ≤ k := div_nonneg hC₀ hdenLp.le
  have hb0 : 0 ≤ b := mul_nonneg hx0 hk0
  have hT0 : 0 ≤ T := by dsimp only [T]; positivity
  have weighted := Shao.OQ6.WeightedDeletionMoments.actual_quadratic_weighted_deletion_bounds
    μ h hh hh2 hhsymm hcenter hprojectionsecond n hn x hx0 hwindow
  rcases weighted with ⟨hSigned, hDI, hDB, hXI, hXB, hLI, hLB⟩
  change (∀ i : Fin n, Integrable
    (fun ξ => R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|) P₀) at hDI
  change (∑ i : Fin n, ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀) ≤
    4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / t at hDB
  change (∀ i : Fin n, Integrable (fun ξ => V ξ i) P₀) at hLI
  change (∑ i : Fin n, ∫ ξ, V ξ i ∂P₀) ≤
    24 * C ^ 2 * s ^ 2 * N ^ 2 * (1 + x) ^ 2 at hLB
  -- First establish all genuine L1 statements. No signed integral is split yet.
  have hFI : Integrable F Pₐ := hF2.integrable (by norm_num)
  have hAI : Integrable A Pₐ := by
    simpa only [A, D₁] using (hFI.div_const d).abs
  have hD3I : Integrable D₃ Pₐ := by
    exact ((integrable_const (s * x / t)).add
      (hΛ.div_const (s * x * K))).const_mul C₀
  have hfullI : Integrable fullTest Pₐ :=
    (hAI.const_mul x).add (hD3I.const_mul (x ^ 2))
  have hRawFull : Integrable (fun ξ => fullTest ξ * Real.exp (S ξ)) P₀ := by
    have hi : Integrable (fun ξ => Real.exp (S ξ) * fullTest ξ) P₀ := by
      simpa only [smul_eq_mul] using
        (integrable_tilted_iff hFullExp fullTest).mp hfullI
    exact hi.congr (Filter.Eventually.of_forall fun ξ => mul_comm _ _)
  have hEdgeM (j l : Fin n) : Measurable (fun ξ : Fin n → Ω => e ξ j l) := by
    have hsel : Measurable (fun ξ : Fin n → Ω => (ξ j, ξ l)) :=
      (measurable_pi_apply j).prodMk (measurable_pi_apply l)
    simpa only [e, Function.comp_def] using hr.comp hsel
  have hEraseM (i j l : Fin n) : Measurable
      (fun ξ : Fin n → Ω => Shao.OQ6.ResidualDeletion.eraseIncident (e ξ) i j l) := by
    by_cases hi : j = i ∨ l = i
    · simpa only [Shao.OQ6.ResidualDeletion.eraseIncident, if_pos hi] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
    · simpa only [Shao.OQ6.ResidualDeletion.eraseIncident, if_neg hi] using hEdgeM j l
  have hFM : Measurable F := by
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro l hl
    by_cases hjl : j < l
    · simpa only [if_pos hjl] using hEdgeM j l
    · simpa only [if_neg hjl] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
  have hFdelM (i : Fin n) : Measurable (fun ξ => Fdel ξ i) := by
    apply Finset.measurable_sum
    intro j hj
    apply Finset.measurable_sum
    intro l hl
    by_cases hjl : j < l
    · simpa only [if_pos hjl] using hEraseM i j l
    · simpa only [if_neg hjl] using
        (measurable_const : Measurable (fun _ : Fin n → Ω => (0 : ℝ)))
  have hAM : Measurable A := by
    simpa only [A, D₁, Real.norm_eq_abs] using (hFM.div_const d).norm
  have hAdelM (i : Fin n) : Measurable (fun ξ => Adel ξ i) := by
    simpa only [Adel, D₁del, Real.norm_eq_abs] using ((hFdelM i).div_const d).norm
  have hφM : Measurable φ :=
    (hg.const_mul a).sub (((hg.const_mul a).pow_const (2 : ℕ)).div_const 2)
  have hRM (i : Fin n) : Measurable (fun ξ => R ξ i) := by
    have hm : Measurable (fun ξ : Fin n → Ω => Sminus ξ i) :=
      Finset.measurable_sum _ (fun j hj => hφM.comp (measurable_pi_apply j))
    exact hm.exp.div_const I
  have hcapM (i : Fin n) : Measurable (fun ξ => cap ξ i) := by
    simpa only [cap, Real.norm_eq_abs, Function.comp_apply] using
      ((hg.comp (measurable_pi_apply i)).const_mul a).norm.min measurable_const
  have hR0 (ξ : Fin n → Ω) (i : Fin n) : 0 ≤ R ξ i :=
    div_nonneg (Real.exp_pos _).le hFullPos.le
  have hcap0 (ξ : Fin n → Ω) (i : Fin n) : 0 ≤ cap ξ i :=
    le_min (abs_nonneg _) (by norm_num)
  have hU0 (ξ : Fin n → Ω) (i : Fin n) : 0 ≤ U ξ i :=
    mul_nonneg (mul_nonneg (hR0 ξ i) (hcap0 ξ i)) (abs_nonneg _)
  have hUle (ξ : Fin n → Ω) (i : Fin n) :
      U ξ i ≤ R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| := by
    exact mul_le_mul_of_nonneg_left
      (abs_abs_sub_abs_le_abs_sub (D₁ ξ) (D₁del ξ i))
      (mul_nonneg (hR0 ξ i) (hcap0 ξ i))
  have hUI (i : Fin n) : Integrable (fun ξ => U ξ i) P₀ := by
    have hUM : Measurable (fun ξ => U ξ i) := by
      change Measurable (fun ξ => R ξ i * cap ξ i * |A ξ - Adel ξ i|)
      have hAbsM : Measurable (fun ξ => |A ξ - Adel ξ i|) := by
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hAM.sub (hAdelM i)).norm
      exact ((hRM i).mul (hcapM i)).mul hAbsM
    apply (hDI i).mono' hUM.aestronglyMeasurable
    exact Filter.Eventually.of_forall fun ξ => by
      change |U ξ i| ≤ R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i|
      rw [abs_of_nonneg (hU0 ξ i)]
      exact hUle ξ i
  have hD3abs (ξ : Fin n → Ω) (i : Fin n) :
      |D₃ ξ - D₃del ξ i| = k * |Λsq ξ - Λdelsq ξ i| := by
    have heq : D₃ ξ - D₃del ξ i = k * (Λsq ξ - Λdelsq ξ i) := by
      dsimp only [D₃, D₃del, k, K, N, t]
      ring
    rw [heq, abs_mul, abs_of_nonneg hk0]
  have hDeletePoint (ξ : Fin n → Ω) (i : Fin n) :
      R ξ i * deletedTest ξ i = U ξ i + b * V ξ i := by
    change R ξ i * (cap ξ i *
      (|A ξ - Adel ξ i| + x * |D₃ ξ - D₃del ξ i|)) = _
    rw [hD3abs]
    dsimp only [U, V, b]
    ring
  have hDeleteI (i : Fin n) : Integrable
      (fun ξ => R ξ i * deletedTest ξ i) P₀ := by
    exact ((hUI i).add ((hLI i).const_mul b)).congr
      (Filter.Eventually.of_forall fun ξ => (hDeletePoint ξ i).symm)
  have hRawDelete (i : Fin n) : Integrable
      (fun ξ => deletedTest ξ i * Real.exp (Sminus ξ i)) P₀ := by
    exact ((hDeleteI i).const_mul I).congr
      (Filter.Eventually.of_forall fun ξ => by
        change I * (Real.exp (Sminus ξ i) / I * deletedTest ξ i) = _
        field_simp [hFullPos.ne']
        <;> ring)
  -- Every displayed raw integrand is now genuinely integrable.
  have hFullNormalized :
      (∫ ξ, fullTest ξ * Real.exp (S ξ) ∂P₀) / I = ∫ ξ, fullTest ξ ∂Pₐ := by
    change _ = ∫ ξ, fullTest ξ ∂P₀.tilted S
    rw [integral_tilted, hFullNorm]
    calc
      _ = ∫ ξ, (fullTest ξ * Real.exp (S ξ)) / I ∂P₀ := by
        simp only [div_eq_mul_inv, integral_mul_const]
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
        simp only [smul_eq_mul]
        ring)
  have hDeleteNormalized (i : Fin n) :
      (∫ ξ, deletedTest ξ i * Real.exp (Sminus ξ i) ∂P₀) / I =
        ∫ ξ, R ξ i * deletedTest ξ i ∂P₀ := by
    calc
      _ = ∫ ξ, (deletedTest ξ i * Real.exp (Sminus ξ i)) / I ∂P₀ := by
        simp only [div_eq_mul_inv, integral_mul_const]
      _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun ξ => by
        dsimp only [R]
        ring)
  have hFullSplit : (∫ ξ, fullTest ξ ∂Pₐ) =
      x * (∫ ξ, A ξ ∂Pₐ) + x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) := by
    rw [show fullTest = (fun ξ => x * A ξ + x ^ 2 * D₃ ξ) from rfl,
      integral_add (hAI.const_mul x) (hD3I.const_mul (x ^ 2)),
      integral_const_mul, integral_const_mul]
  have hCostIdentity : sourceCost =
      x * (∫ ξ, A ξ ∂Pₐ) + x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) +
        ∑ i : Fin n, ∫ ξ, R ξ i * deletedTest ξ i ∂P₀ := by
    change ((∫ ξ, fullTest ξ * Real.exp (S ξ) ∂P₀) +
      ∑ i : Fin n, ∫ ξ, deletedTest ξ i * Real.exp (Sminus ξ i) ∂P₀) / I = _
    rw [add_div, hFullNormalized, Finset.sum_div]
    simp_rw [hDeleteNormalized]
    rw [hFullSplit]
  have hDeleteSplit :
      (∑ i : Fin n, ∫ ξ, R ξ i * deletedTest ξ i ∂P₀) =
        (∑ i : Fin n, ∫ ξ, U ξ i ∂P₀) +
          b * (∑ i : Fin n, ∫ ξ, V ξ i ∂P₀) := by
    simp_rw [hDeletePoint]
    rw [show (∑ i : Fin n, ∫ ξ, U ξ i + b * V ξ i ∂P₀) =
      ∑ i : Fin n, ((∫ ξ, U ξ i ∂P₀) + b * (∫ ξ, V ξ i ∂P₀)) by
        apply Finset.sum_congr rfl
        intro i hi
        rw [integral_add (hUI i) ((hLI i).const_mul b), integral_const_mul]]
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  -- Probability Cauchy--Schwarz requires only the genuine pair L2 input.
  have hFmeanCS : (∫ ξ, |F ξ| ∂Pₐ) ≤ Real.sqrt (∫ ξ, F ξ ^ 2 ∂Pₐ) := by
    have hhCS := integral_mul_norm_le_Lp_mul_Lq
      (Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩ :
        (2 : ℝ).HolderConjugate 2)
      (by simpa using hF2)
      (by simpa using (memLp_const (1 : ℝ) :
        MemLp (fun _ : Fin n → Ω => (1 : ℝ)) 2 Pₐ))
    simpa only [norm_mul, Real.norm_eq_abs, Real.rpow_two, ← Real.sqrt_eq_rpow,
      sq_abs, norm_one, one_pow, integral_const, probReal_univ, one_smul,
      Real.sqrt_one, mul_one] using hhCS
  have hFmean : (∫ ξ, |F ξ| ∂Pₐ) ≤ 4 * C ^ 2 * s * N * (1 + x ^ 2) := by
    have hpoly : 14 * (1 + x ^ 4) ≤ 16 * (1 + x ^ 2) ^ 2 := by
      nlinarith only [sq_nonneg x, sq_nonneg (x ^ 2)]
    have hsq : (∫ ξ, F ξ ^ 2 ∂Pₐ) ≤
        (4 * C ^ 2 * s * N * (1 + x ^ 2)) ^ 2 := by
      have hhpoly := mul_le_mul_of_nonneg_left hpoly
        (show 0 ≤ C ^ 4 * s ^ 2 * N ^ 2 by positivity)
      nlinarith only [hFfinal, hhpoly]
    calc
      _ ≤ Real.sqrt (∫ ξ, F ξ ^ 2 ∂Pₐ) := hFmeanCS
      _ ≤ Real.sqrt ((4 * C ^ 2 * s * N * (1 + x ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt hsq
      _ = _ := Real.sqrt_sq (by positivity)
  have hAmean : (∫ ξ, A ξ ∂Pₐ) ≤
      (4 * C ^ 2 * s * N * (1 + x ^ 2)) / d := by
    calc
      _ = (∫ ξ, |F ξ| ∂Pₐ) / d := by
        have hApoint (ξ : Fin n → Ω) : A ξ = |F ξ| / d := by
          change |F ξ / d| = |F ξ| / d
          rw [abs_div, abs_of_pos hdp]
        calc
          _ = ∫ ξ, |F ξ| / d ∂Pₐ :=
            integral_congr_ae (Filter.Eventually.of_forall hApoint)
          _ = _ := by simp only [div_eq_mul_inv, integral_mul_const]
      _ ≤ _ := div_le_div_of_nonneg_right hFmean hdp.le
  have hpolyx : x * (1 + x ^ 2) ≤ (1 + x) ^ 3 := by
    nlinarith only [hx0, sq_nonneg x]
  have hFullA : x * (∫ ξ, A ξ ∂Pₐ) ≤ 8 * C ^ 2 * T := by
    have hNr : N ≤ 2 * (N - 1) := by linarith only [hN3]
    have hpN : x * (1 + x ^ 2) * N ≤ 2 * (1 + x) ^ 3 * (N - 1) := by
      calc
        _ ≤ (1 + x) ^ 3 * N := mul_le_mul_of_nonneg_right hpolyx hN0
        _ ≤ _ := by
          have hhNr := mul_le_mul_of_nonneg_left hNr
            (show 0 ≤ (1 + x) ^ 3 by positivity)
          nlinarith only [hhNr]
    calc
      _ ≤ x * ((4 * C ^ 2 * s * N * (1 + x ^ 2)) / d) :=
        mul_le_mul_of_nonneg_left hAmean hx0
      _ = (4 * C ^ 2 * s * (x * (1 + x ^ 2)) * N) / (t * (N - 1)) := by
        dsimp only [d]
        ring
      _ ≤ (8 * C ^ 2 * s * (1 + x) ^ 3) / t := by
        apply (div_le_div_iff₀ hdp htp).mpr
        have hhpoly := mul_le_mul_of_nonneg_left hpN
          (show 0 ≤ 4 * C ^ 2 * s * t by positivity)
        nlinarith only [hhpoly]
      _ = _ := by dsimp only [T]; ring
  have hD3mean : (∫ ξ, D₃ ξ ∂Pₐ) =
      C₀ * (s * x / t + (∫ ξ, Λsq ξ ∂Pₐ) / (s * x * K)) := by
    change (∫ ξ, C₀ * (s * x / t + Λsq ξ / (s * x * K)) ∂Pₐ) = _
    rw [integral_const_mul,
      integral_add (integrable_const _) (hΛ.div_const (s * x * K))]
    simp only [integral_const, probReal_univ, one_smul, div_eq_mul_inv, integral_mul_const]
  have hFullD3 : x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) ≤
      C₀ * (1 + 14 * C ^ 4) * T := by
    have hpoly3 : x ^ 3 ≤ (1 + x) ^ 3 := by nlinarith only [hx0, sq_nonneg x]
    calc
      _ = x ^ 2 * (C₀ * (s * x / t + (∫ ξ, Λsq ξ ∂Pₐ) / (s * x * K))) :=
        by rw [hD3mean]
      _ ≤ x ^ 2 * (C₀ * (s * x / t +
          (14 * C ^ 4 * s ^ 2 * N ^ 2 * (1 + x ^ 2)) / (s * x * K))) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left
            (add_le_add (le_refl (s * x / t))
              (div_le_div_of_nonneg_right hΛfinal hdenLp.le)) hC₀)
          (sq_nonneg x)
      _ = C₀ * s * (x ^ 3 + 14 * C ^ 4 * (x * (1 + x ^ 2))) / t := by
        dsimp only [K]
        field_simp [hsp.ne', hxp.ne', hNp.ne', htp.ne']
        <;> ring
      _ ≤ C₀ * s * ((1 + x) ^ 3 + 14 * C ^ 4 * (1 + x) ^ 3) / t := by
        apply div_le_div_of_nonneg_right _ htp.le
        exact mul_le_mul_of_nonneg_left
          (add_le_add hpoly3
            (mul_le_mul_of_nonneg_left hpolyx (by positivity)))
          (mul_nonneg hC₀ hsp.le)
      _ = _ := by dsimp only [T]; ring
  have hDeletedA : (∑ i : Fin n, ∫ ξ, U ξ i ∂P₀) ≤ 6 * C * T := by
    have hrt : 4 * Real.sqrt 2 ≤ (6 : ℝ) := by
      have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
        calc
          _ ≤ Real.sqrt ((3 / 2 : ℝ) ^ 2) := Real.sqrt_le_sqrt (by norm_num)
          _ = _ := Real.sqrt_sq (by norm_num)
      linarith only [hsqrt]
    have hpow : (1 + x) ^ 2 ≤ (1 + x) ^ 3 := by
      have hhpow := mul_nonneg (sq_nonneg (1 + x)) hx0
      nlinarith only [hhpow]
    calc
      _ ≤ ∑ i : Fin n, ∫ ξ, R ξ i * cap ξ i * |D₁ ξ - D₁del ξ i| ∂P₀ :=
        Finset.sum_le_sum (fun i hi => integral_mono (hUI i) (hDI i) (fun ξ => hUle ξ i))
      _ ≤ 4 * Real.sqrt 2 * C * s * (1 + x) ^ 2 / t := hDB
      _ ≤ 6 * C * s * (1 + x) ^ 2 / t := by
        apply div_le_div_of_nonneg_right _ htp.le
        have hhroot := mul_le_mul_of_nonneg_right hrt
          (show 0 ≤ C * s * (1 + x) ^ 2 by positivity)
        nlinarith only [hhroot]
      _ ≤ 6 * C * s * (1 + x) ^ 3 / t := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) htp.le
      _ = _ := by dsimp only [T]; ring
  have hDeletedD3 : b * (∑ i : Fin n, ∫ ξ, V ξ i ∂P₀) ≤
      24 * C ^ 2 * C₀ * T := by
    have hpow : (1 + x) ^ 2 ≤ (1 + x) ^ 3 := by
      have hhpow := mul_nonneg (sq_nonneg (1 + x)) hx0
      nlinarith only [hhpow]
    calc
      _ ≤ b * (24 * C ^ 2 * s ^ 2 * N ^ 2 * (1 + x) ^ 2) :=
        mul_le_mul_of_nonneg_left hLB hb0
      _ = 24 * C ^ 2 * C₀ * s * (1 + x) ^ 2 / t := by
        dsimp only [b, k, K]
        field_simp [hsp.ne', hxp.ne', hNp.ne', htp.ne']
        <;> ring
      _ ≤ 24 * C ^ 2 * C₀ * s * (1 + x) ^ 3 / t := by
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow (by positivity)) htp.le
      _ = _ := by dsimp only [T]; ring
  have hC21 : 1 ≤ C ^ 2 := by nlinarith only [hC1, sq_nonneg (C - 1)]
  have hC12 : C ≤ C ^ 2 := by nlinarith only [hC1, sq_nonneg (C - 1)]
  have hC24 : C ^ 2 ≤ C ^ 4 := by
    have hhC := mul_nonneg (sq_nonneg C) (sub_nonneg.mpr hC21)
    nlinarith only [hhC]
  have hC14 : 1 ≤ C ^ 4 := hC21.trans hC24
  have hCC4 : C ≤ C ^ 4 := hC12.trans hC24
  have hCoefficient :
      8 * C ^ 2 + C₀ * (1 + 14 * C ^ 4) + 6 * C + 24 * C ^ 2 * C₀ ≤
        64 * C ^ 4 * (1 + C₀) := by
    have h8 := mul_le_mul_of_nonneg_left hC24 (by norm_num : (0 : ℝ) ≤ 8)
    have h6 := mul_le_mul_of_nonneg_left hCC4 (by norm_num : (0 : ℝ) ≤ 6)
    have h1 := mul_le_mul_of_nonneg_left hC14 hC₀
    have h24 := mul_le_mul_of_nonneg_left hC24 (show 0 ≤ 24 * C₀ by positivity)
    have hExtra : 0 ≤ C ^ 4 * C₀ := mul_nonneg (by positivity) hC₀
    nlinarith only [h8, h6, h1, h24, hC14, hExtra]
  refine ⟨hRawFull, hRawDelete, hCostIdentity, ?_⟩
  calc
    sourceCost = x * (∫ ξ, A ξ ∂Pₐ) + x ^ 2 * (∫ ξ, D₃ ξ ∂Pₐ) +
        ((∑ i : Fin n, ∫ ξ, U ξ i ∂P₀) + b * (∑ i : Fin n, ∫ ξ, V ξ i ∂P₀)) := by
      rw [hCostIdentity, hDeleteSplit]
    _ ≤ (8 * C ^ 2 + C₀ * (1 + 14 * C ^ 4) + 6 * C + 24 * C ^ 2 * C₀) * T := by
      have hhbound := add_le_add (add_le_add hFullA hFullD3)
        (add_le_add hDeletedA hDeletedD3)
      nlinarith only [hhbound]
    _ ≤ (64 * C ^ 4 * (1 + C₀)) * T :=
      mul_le_mul_of_nonneg_right hCoefficient hT0
    _ = _ := by dsimp only [T]; ring

end

end Shao.OQ6.SourceAnalyticCost
