import Shao.OQ6.ActualMomentNormalization
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Monoid.Defs
import Mathlib.Topology.Algebra.Order.Group
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

set_option autoImplicit false

namespace Shao.OQ6.NormalizedRemainderEnvelope

noncomputable section

open MeasureTheory
open scoped BigOperators Classical Topology

theorem actual_energy_envelope_integrability
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (B : Ω → ℝ) (hB : Measurable B)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hBint : Integrable B ν) :
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let C : Ω → ℝ := fun ω => Real.sqrt (1 + B ω)
    let H : ℝ → Ω → ℝ := fun z ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
    let ρ : ℝ → ℝ := fun ε => 4 * ε * Real.sqrt (n : ℝ)
    Measurable V ∧
    (∀ ω : Ω, 0 ≤ V ω) ∧
    (∀ ω : Ω, (V ω) ^ 2 = ∑ i : Fin n, (ξ i ω) ^ 2) ∧
    MemLp V 2 ν ∧
    Integrable V ν ∧
    Integrable (fun ω => (V ω) ^ 2) ν ∧
    (∫ ω, (V ω) ^ 2 ∂ν) = 1 ∧
    Measurable C ∧
    (∀ ω : Ω, 1 ≤ C ω) ∧
    (∀ ω : Ω, (C ω) ^ 2 = 1 + B ω) ∧
    MemLp C 2 ν ∧
    Integrable C ν ∧
    Integrable (fun ω => (C ω) ^ 2) ν ∧
    (∫ ω, (C ω) ^ 2 ∂ν) = 1 + (∫ ω, B ω ∂ν) ∧
    MemLp (fun ω => 1 + V ω) 2 ν ∧
    Integrable (fun ω => (1 + V ω) * C ω) ν ∧
    (∀ z : ℝ, Measurable (H z) ∧ Integrable (H z) ν) ∧
    (∀ (z : ℝ), 0 ≤ z → ∀ ω : Ω, 0 < H z ω) ∧
    (∀ (z ε : ℝ), Integrable (fun ω => |ρ ε * H z ω|) ν) ∧
    (∀ (z : ℝ), 0 ≤ z → ∀ ε : ℝ,
      (∫ ω, |ρ ε * H z ω| ∂ν) = |ρ ε| * (∫ ω, H z ω ∂ν)) ∧
    (∀ (z : ℝ), 0 ≤ z →
      Filter.Tendsto (fun ε : ℝ => ∫ ω, |ρ ε * H z ω| ∂ν)
        (nhds (0 : ℝ)) (nhds (0 : ℝ))) := by
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let C : Ω → ℝ := fun ω => Real.sqrt (1 + B ω)
  let H : ℝ → Ω → ℝ := fun z ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
  let ρ : ℝ → ℝ := fun ε => 4 * ε * Real.sqrt (n : ℝ)
  have hVm : Measurable V := by
    exact (Finset.measurable_sum Finset.univ (fun i _ => (hξ i).pow_const (2 : ℕ))).sqrt
  have hVnonneg : ∀ ω : Ω, 0 ≤ V ω := fun ω => Real.sqrt_nonneg _
  have hVsq : ∀ ω : Ω, (V ω) ^ 2 = ∑ i : Fin n, (ξ i ω) ^ 2 := by
    intro ω
    exact Real.sq_sqrt (Finset.sum_nonneg (fun i _ => sq_nonneg (ξ i ω)))
  have hsumInt : Integrable (fun ω => ∑ i : Fin n, (ξ i ω) ^ 2) ν := by
    exact integrable_finsetSum Finset.univ (fun i _ => (hξ2 i).integrable_sq)
  have hV2int : Integrable (fun ω => (V ω) ^ 2) ν := by
    rw [show (fun ω => (V ω) ^ 2) =
      (fun ω => ∑ i : Fin n, (ξ i ω) ^ 2) from funext hVsq]
    exact hsumInt
  have hVlp : MemLp V 2 ν :=
    (memLp_two_iff_integrable_sq hVm.aestronglyMeasurable).2 hV2int
  have hVint : Integrable V ν := MemLp.integrable (by norm_num) hVlp
  have hVE : (∫ ω, (V ω) ^ 2 ∂ν) = 1 := by
    calc
      (∫ ω, (V ω) ^ 2 ∂ν) =
          ∫ ω, ∑ i : Fin n, (ξ i ω) ^ 2 ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hVsq)
      _ = ∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν :=
        integral_finsetSum Finset.univ (fun i _ => (hξ2 i).integrable_sq)
      _ = 1 := hξenergy
  have hCm : Measurable C := (measurable_const.add hB).sqrt
  have hCone : ∀ ω : Ω, 1 ≤ C ω := by
    intro ω
    calc
      (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ C ω := Real.sqrt_le_sqrt (by linarith [hBnonneg ω])
  have hCsq : ∀ ω : Ω, (C ω) ^ 2 = 1 + B ω := by
    intro ω
    exact Real.sq_sqrt (by linarith [hBnonneg ω])
  have honeBInt : Integrable (fun ω => 1 + B ω) ν :=
    (integrable_const (1 : ℝ)).add hBint
  have hC2int : Integrable (fun ω => (C ω) ^ 2) ν := by
    rw [show (fun ω => (C ω) ^ 2) = (fun ω => 1 + B ω) from funext hCsq]
    exact honeBInt
  have hClp : MemLp C 2 ν :=
    (memLp_two_iff_integrable_sq hCm.aestronglyMeasurable).2 hC2int
  have hCint : Integrable C ν := MemLp.integrable (by norm_num) hClp
  have hCE : (∫ ω, (C ω) ^ 2 ∂ν) = 1 + (∫ ω, B ω ∂ν) := by
    calc
      (∫ ω, (C ω) ^ 2 ∂ν) = ∫ ω, 1 + B ω ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hCsq)
      _ = (∫ _ : Ω, (1 : ℝ) ∂ν) + (∫ ω, B ω ∂ν) :=
        integral_add (integrable_const (1 : ℝ)) hBint
      _ = 1 + (∫ ω, B ω ∂ν) := by simp
  have hOneVlp : MemLp (fun ω => 1 + V ω) 2 ν := by
    have h : MemLp ((fun _ : Ω => (1 : ℝ)) + V) 2 ν :=
      (memLp_const (1 : ℝ)).add hVlp
    change MemLp (fun ω => 1 + V ω) 2 ν at h
    exact h
  have hOneVInt : Integrable (fun ω => 1 + V ω) ν :=
    MemLp.integrable (by norm_num) hOneVlp
  have hprodInt : Integrable (fun ω => (1 + V ω) * C ω) ν := by
    have h := hOneVlp.integrable_mul hClp
    change Integrable (fun ω => (1 + V ω) * C ω) ν at h
    exact h
  have hHm : ∀ z : ℝ, Measurable (H z) := by
    intro z
    exact (measurable_const.add hVm).mul
      (measurable_const.add (measurable_const.mul hCm))
  have hHint : ∀ z : ℝ, Integrable (H z) ν := by
    intro z
    have h : Integrable (fun ω =>
        (1 + V ω) * Real.sqrt (n : ℝ) + z * ((1 + V ω) * C ω)) ν :=
      (hOneVInt.mul_const (Real.sqrt (n : ℝ))).add (hprodInt.const_mul z)
    rw [show H z = (fun ω =>
      (1 + V ω) * Real.sqrt (n : ℝ) + z * ((1 + V ω) * C ω)) by
      funext ω
      dsimp only [H]
      ring]
    exact h
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hHpos : ∀ (z : ℝ), 0 ≤ z → ∀ ω : Ω, 0 < H z ω := by
    intro z hz ω
    have hOneVpos : 0 < 1 + V ω := by linarith [hVnonneg ω]
    have hzC : 0 ≤ z * C ω := mul_nonneg hz (by linarith [hCone ω])
    exact mul_pos hOneVpos (add_pos_of_pos_of_nonneg hnsqrt hzC)
  have hAbsInt : ∀ (z ε : ℝ), Integrable (fun ω => |ρ ε * H z ω|) ν := by
    intro z ε
    simpa only [Real.norm_eq_abs] using ((hHint z).const_mul (ρ ε)).norm
  have hAbsIntegral : ∀ (z : ℝ), 0 ≤ z → ∀ ε : ℝ,
      (∫ ω, |ρ ε * H z ω| ∂ν) = |ρ ε| * (∫ ω, H z ω ∂ν) := by
    intro z hz ε
    calc
      (∫ ω, |ρ ε * H z ω| ∂ν) = ∫ ω, |ρ ε| * H z ω ∂ν := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall (fun ω => by
          change |ρ ε * H z ω| = |ρ ε| * H z ω
          exact (abs_mul (ρ ε) (H z ω)).trans
            (congrArg (fun t : ℝ => |ρ ε| * t)
              (abs_of_nonneg (hHpos z hz ω).le)))
      _ = |ρ ε| * (∫ ω, H z ω ∂ν) := integral_const_mul (abs (ρ ε)) (H z)
  have hLimit : ∀ (z : ℝ), 0 ≤ z →
      Filter.Tendsto (fun ε : ℝ => ∫ ω, |ρ ε * H z ω| ∂ν)
        (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
    intro z hz
    have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhds (0 : ℝ)) (nhds (0 : ℝ)) :=
      Filter.tendsto_id
    have hρ : Filter.Tendsto ρ (nhds (0 : ℝ)) (nhds (0 : ℝ)) := by
      simpa only [ρ, mul_zero, zero_mul] using
        (Filter.Tendsto.mul_const (Real.sqrt (n : ℝ))
          (Filter.Tendsto.const_mul (4 : ℝ) hid))
    have h := Filter.Tendsto.mul_const (∫ ω, H z ω ∂ν) hρ.abs
    rw [show (fun ε : ℝ => ∫ ω, |ρ ε * H z ω| ∂ν) =
      (fun ε : ℝ => |ρ ε| * (∫ ω, H z ω ∂ν)) from funext (hAbsIntegral z hz)]
    simpa only [abs_zero, zero_mul] using h
  exact ⟨hVm, hVnonneg, hVsq, hVlp, hVint, hV2int, hVE, hCm, hCone,
    hCsq, hClp, hCint, hC2int, hCE, hOneVlp, hprodInt,
    (fun z => ⟨hHm z, hHint z⟩), hHpos, hAbsInt, hAbsIntegral, hLimit⟩

theorem actual_normalized_remainder_envelope_spec
    {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (n : ℕ) (hn : 1 ≤ n) (ξ Y : Fin n → Ω → ℝ)
    (hξ : ∀ i : Fin n, Measurable (ξ i))
    (hξ2 : ∀ i : Fin n, MemLp (ξ i) 2 ν)
    (hξmean : ∀ i : Fin n, (∫ ω, ξ i ω ∂ν) = 0)
    (hξenergy : (∑ i : Fin n, ∫ ω, (ξ i ω) ^ 2 ∂ν) = 1)
    (hY : ∀ i : Fin n, Measurable (Y i))
    (D1 D2 A B : Ω → ℝ)
    (Adelete Bdelete : Fin n → Ω → ℝ)
    (hD1 : Measurable D1) (hD2 : Measurable D2)
    (hA : Measurable A) (hB : Measurable B)
    (hAnonneg : ∀ ω : Ω, 0 ≤ A ω)
    (hBnonneg : ∀ ω : Ω, 0 ≤ B ω)
    (hD1A : ∀ ω : Ω, |D1 ω| ≤ A ω)
    (hD2B : ∀ ω : Ω, |D2 ω| ≤ B ω)
    (hAint : Integrable A ν) (hBint : Integrable B ν)
    (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / (4 * Real.sqrt (n : ℝ)))
    (herr : ∀ (i : Fin n) (ω : Ω), |Y i ω - ξ i ω| ≤ ε)
    (z : ℝ) (hz : 0 ≤ z) :
    let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
    let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
    let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
    let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
    let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
    let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
    let C : Ω → ℝ := fun ω => Real.sqrt (1 + B ω)
    let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
    let ρ : ℝ := 4 * ε * Real.sqrt (n : ℝ)
    let Dη : Ω → ℝ := fun ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
    let Aε : Ω → ℝ := fun ω => A ω + ρ * H ω
    let Bε : Ω → ℝ := B
    let Aεdelete : Fin n → Ω → ℝ := Adelete
    let Bεdelete : Fin n → Ω → ℝ := Bdelete
    (∀ i : Fin n, Measurable (η i)) ∧
    Measurable W ∧ Measurable Wη ∧ Measurable V ∧ Measurable Vη ∧
    Measurable b ∧ Measurable C ∧ Measurable H ∧ Measurable Dη ∧
    Measurable Aε ∧ Measurable Bε ∧
    (∀ ω : Ω, 0 ≤ b ω ∧ b ω ≤ C ω) ∧
    (∀ ω : Ω, 0 < H ω) ∧
    0 < ρ ∧ ρ < 1 ∧
    Integrable H ν ∧
    Integrable D1 ν ∧
    Integrable Dη ν ∧
    Integrable Aε ν ∧
    Integrable (fun ω => Dη ω - D1 ω) ν ∧
    Integrable (fun ω => |Dη ω - D1 ω|) ν ∧
    Integrable (fun ω => ρ * H ω) ν ∧
    Integrable (fun ω => A ω + H ω) ν ∧
    (∀ ω : Ω, |Dη ω - D1 ω| ≤ ρ * H ω) ∧
    (∀ ω : Ω, |Dη ω| ≤ Aε ω) ∧
    (∀ ω : Ω, 0 ≤ Aε ω) ∧
    (∀ ω : Ω, Aε ω ≤ A ω + H ω) ∧
    (∀ ω : Ω, 0 ≤ Bε ω ∧ |D2 ω| ≤ Bε ω) ∧
    Bε = B ∧ Aεdelete = Adelete ∧ Bεdelete = Bdelete ∧
    (∀ (i : Fin n) (ω : Ω),
      |Aε ω - Aεdelete i ω| ≤ |A ω - Adelete i ω| + ρ * H ω) ∧
    (∀ (i : Fin n) (ω : Ω),
      |Bε ω - Bεdelete i ω| = |B ω - Bdelete i ω|) ∧
    (∫ ω, |Dη ω - D1 ω| ∂ν) ≤ ρ * (∫ ω, H ω ∂ν) ∧
    (∫ ω, |Aε ω - A ω| ∂ν) = ρ * (∫ ω, H ω ∂ν) ∧
    (∫ ω, Aε ω ∂ν) = (∫ ω, A ω ∂ν) + ρ * (∫ ω, H ω ∂ν) := by
  let η : Fin n → Ω → ℝ := Shao.OQ6.ActualMomentNormalization.actualNormalizedFamily ν Y
  let W : Ω → ℝ := fun ω => ∑ i : Fin n, ξ i ω
  let Wη : Ω → ℝ := fun ω => ∑ i : Fin n, η i ω
  let V : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (ξ i ω) ^ 2)
  let Vη : Ω → ℝ := fun ω => Real.sqrt (∑ i : Fin n, (η i ω) ^ 2)
  let b : Ω → ℝ := fun ω => Real.sqrt (1 + D2 ω)
  let C : Ω → ℝ := fun ω => Real.sqrt (1 + B ω)
  let H : Ω → ℝ := fun ω => (1 + V ω) * (Real.sqrt (n : ℝ) + z * C ω)
  let ρ : ℝ := 4 * ε * Real.sqrt (n : ℝ)
  let Dη : Ω → ℝ := fun ω => D1 ω + W ω - Wη ω + z * b ω * (Vη ω - V ω)
  let Aε : Ω → ℝ := fun ω => A ω + ρ * H ω
  let Bε : Ω → ℝ := B
  let Aεdelete : Fin n → Ω → ℝ := Adelete
  let Bεdelete : Fin n → Ω → ℝ := Bdelete
  have hnorm := Shao.OQ6.ActualMomentNormalization.actual_moment_normalization_spec
    ν n hn ξ Y hξ hξ2 hξmean hξenergy hY ε hε hεsmall herr
  rcases hnorm with ⟨_, hηm, _, _, _, _, _, _, _, hVerr, hWerr, _, _⟩
  have henergy := actual_energy_envelope_integrability
    ν n hn ξ hξ hξ2 hξenergy B hB hBnonneg hBint
  rcases henergy with
    ⟨hVm, hVnonneg, _, _, _, _, _, hCm, hCone, _, _, _, _, _, _, _,
      hHspec, hHpositive, _, _, _⟩
  have hHm : Measurable H := (hHspec z).1
  have hHint : Integrable H ν := (hHspec z).2
  have hHpos : ∀ ω : Ω, 0 < H ω := hHpositive z hz
  have hWm : Measurable W :=
    Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hWηm : Measurable Wη :=
    Finset.measurable_sum Finset.univ (fun i _ => hηm i)
  have hVηm : Measurable Vη :=
    (Finset.measurable_sum Finset.univ (fun i _ => (hηm i).pow_const (2 : ℕ))).sqrt
  have hbm : Measurable b := (measurable_const.add hD2).sqrt
  have hbbounds : ∀ ω : Ω, 0 ≤ b ω ∧ b ω ≤ C ω := by
    intro ω
    refine ⟨Real.sqrt_nonneg _, ?_⟩
    exact Real.sqrt_le_sqrt
      (add_le_add le_rfl ((le_abs_self (D2 ω)).trans (hD2B ω)))
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hnsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by linarith)
  have hρpos : 0 < ρ := mul_pos (mul_pos (by norm_num) hε) hnsqrt
  have hρlt : ρ < 1 := by
    have hmul : ε * (4 * Real.sqrt (n : ℝ)) < 1 :=
      (lt_div_iff₀ (mul_pos (by norm_num) hnsqrt)).1 hεsmall
    calc
      ρ = ε * (4 * Real.sqrt (n : ℝ)) := by dsimp only [ρ]; ring
      _ < 1 := hmul
  have hDηm : Measurable Dη :=
    ((hD1.add hWm).sub hWηm).add
      ((measurable_const.mul hbm).mul (hVηm.sub hVm))
  have hAεm : Measurable Aε := hA.add (measurable_const.mul hHm)
  have hError : ∀ ω : Ω, |Dη ω - D1 ω| ≤ ρ * H ω := by
    intro ω
    have hzb : 0 ≤ z * b ω := mul_nonneg hz (hbbounds ω).1
    have hzbC : z * b ω ≤ z * C ω :=
      mul_le_mul_of_nonneg_left (hbbounds ω).2 hz
    have hbase : 0 ≤ ρ * (1 + V ω) :=
      mul_nonneg hρpos.le (by linarith [hVnonneg ω])
    calc
      |Dη ω - D1 ω| = |(W ω - Wη ω) + (z * b ω) * (Vη ω - V ω)| := by
        congr 1
        dsimp only [Dη]
        ring
      _ ≤ |W ω - Wη ω| + |(z * b ω) * (Vη ω - V ω)| := abs_add_le _ _
      _ = |Wη ω - W ω| + (z * b ω) * |Vη ω - V ω| := by
        rw [abs_sub_comm (W ω) (Wη ω), abs_mul, abs_of_nonneg hzb]
      _ ≤ Real.sqrt (n : ℝ) * ρ * (1 + V ω) +
          (z * b ω) * (ρ * (1 + V ω)) :=
        add_le_add (hWerr ω) (mul_le_mul_of_nonneg_left (hVerr ω) hzb)
      _ ≤ Real.sqrt (n : ℝ) * ρ * (1 + V ω) +
          (z * C ω) * (ρ * (1 + V ω)) :=
        add_le_add le_rfl (mul_le_mul_of_nonneg_right hzbC hbase)
      _ = ρ * H ω := by dsimp only [H]; ring
  have hD1Int : Integrable D1 ν := by
    apply hAint.mono' hD1.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      simpa only [Real.norm_eq_abs] using hD1A ω)
  have hRInt : Integrable (fun ω => ρ * H ω) ν := hHint.const_mul ρ
  have hδInt : Integrable (fun ω => Dη ω - D1 ω) ν := by
    apply hRInt.mono' (hDηm.sub hD1).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun ω => by
      change ‖Dη ω - D1 ω‖ ≤ ρ * H ω
      rw [Real.norm_eq_abs]
      exact hError ω)
  have hδAbsInt : Integrable (fun ω => |Dη ω - D1 ω|) ν := by
    simpa only [Real.norm_eq_abs] using hδInt.norm
  have hDηInt : Integrable Dη ν := by
    rw [show Dη = (fun ω => D1 ω + (Dη ω - D1 ω)) by
      funext ω
      ring]
    exact hD1Int.add hδInt
  have hAεInt : Integrable Aε ν := hAint.add hRInt
  have hdomInt : Integrable (fun ω => A ω + H ω) ν := hAint.add hHint
  have hEnvelope : ∀ ω : Ω, |Dη ω| ≤ Aε ω := by
    intro ω
    calc
      |Dη ω| = |D1 ω + (Dη ω - D1 ω)| := by congr 1; ring
      _ ≤ |D1 ω| + |Dη ω - D1 ω| := abs_add_le _ _
      _ ≤ A ω + ρ * H ω := add_le_add (hD1A ω) (hError ω)
      _ = Aε ω := rfl
  have hAnonnegε : ∀ ω : Ω, 0 ≤ Aε ω := by
    intro ω
    exact add_nonneg (hAnonneg ω) (mul_nonneg hρpos.le (hHpos ω).le)
  have hAdom : ∀ ω : Ω, Aε ω ≤ A ω + H ω := by
    intro ω
    have hscale : ρ * H ω ≤ 1 * H ω :=
      mul_le_mul_of_nonneg_right hρlt.le (hHpos ω).le
    dsimp only [Aε]
    linarith
  have hDelete : ∀ (i : Fin n) (ω : Ω),
      |Aε ω - Aεdelete i ω| ≤ |A ω - Adelete i ω| + ρ * H ω := by
    intro i ω
    calc
      |Aε ω - Aεdelete i ω| = |(A ω - Adelete i ω) + ρ * H ω| := by
        congr 1
        dsimp only [Aε, Aεdelete]
        ring
      _ ≤ |A ω - Adelete i ω| + |ρ * H ω| := abs_add_le _ _
      _ = |A ω - Adelete i ω| + ρ * H ω := by
        rw [abs_of_nonneg (mul_nonneg hρpos.le (hHpos ω).le)]
  have hIntegralError : (∫ ω, |Dη ω - D1 ω| ∂ν) ≤ ρ * (∫ ω, H ω ∂ν) := by
    calc
      (∫ ω, |Dη ω - D1 ω| ∂ν) ≤ ∫ ω, ρ * H ω ∂ν :=
        integral_mono hδAbsInt hRInt hError
      _ = ρ * (∫ ω, H ω ∂ν) := integral_const_mul ρ H
  have hAerror : ∀ ω : Ω, |Aε ω - A ω| = ρ * H ω := by
    intro ω
    calc
      |Aε ω - A ω| = |ρ * H ω| := by congr 1; dsimp only [Aε]; ring
      _ = ρ * H ω := abs_of_nonneg (mul_nonneg hρpos.le (hHpos ω).le)
  have hIntegralAError : (∫ ω, |Aε ω - A ω| ∂ν) = ρ * (∫ ω, H ω ∂ν) := by
    calc
      (∫ ω, |Aε ω - A ω| ∂ν) = ∫ ω, ρ * H ω ∂ν :=
        integral_congr_ae (Filter.Eventually.of_forall hAerror)
      _ = ρ * (∫ ω, H ω ∂ν) := integral_const_mul ρ H
  have hIntegralA : (∫ ω, Aε ω ∂ν) = (∫ ω, A ω ∂ν) + ρ * (∫ ω, H ω ∂ν) := by
    calc
      (∫ ω, Aε ω ∂ν) = ∫ ω, A ω + ρ * H ω ∂ν := rfl
      _ = (∫ ω, A ω ∂ν) + (∫ ω, ρ * H ω ∂ν) := integral_add hAint hRInt
      _ = (∫ ω, A ω ∂ν) + ρ * (∫ ω, H ω ∂ν) := by rw [integral_const_mul]
  exact ⟨hηm, hWm, hWηm, hVm, hVηm, hbm, hCm, hHm, hDηm, hAεm, hB,
    hbbounds, hHpos, hρpos, hρlt, hHint, hD1Int, hDηInt, hAεInt, hδInt,
    hδAbsInt, hRInt, hdomInt, hError, hEnvelope, hAnonnegε, hAdom,
    (fun ω => ⟨hBnonneg ω, hD2B ω⟩), rfl, rfl, rfl, hDelete,
    (fun _ _ => rfl), hIntegralError, hIntegralAError, hIntegralA⟩

end

end Shao.OQ6.NormalizedRemainderEnvelope
