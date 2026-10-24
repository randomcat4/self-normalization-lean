/- v3: root explicitly contracts the new public API before declaration freeze. Genuine frozen source consumers; current partial coverage is recorded separately. -/
import Shao.Probability.SourceSeparatedOvershoot
import Shao.Probability.SourceIIDGaussianProfileBudget
import Shao.C2.HalfLineGaussianStep
import Shao.C2.SourceHalfLineCompletion
import Shao.C2.HalfLineCompensatedBounds
import Shao.C2.IntervalDerivativeBound

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
noncomputable section
namespace Shao.Probability.SourceActualLocalProfileBudget
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal SourceSeparatedOvershoot
open Shao.C2.BridgeDomination
open scoped BigOperators Classical

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

def wallSigns (J : MonitoredDomain) : Finset ℝ :=
  match J with
  | .upper => {1}
  | .lower => {-1}
  | .interval => {1, -1}

def halflineDerivative (J : MonitoredDomain) : BridgeKernel :=
  match J with
  | .upper => fun p => -Shao.C2.HalfLineMixedProfiles.slopeTime
      (p.1 - p.2.1) (p.1 - p.2.2.2) p.2.2.1
  | .lower => fun p => Shao.C2.HalfLineMixedProfiles.slopeTime
      (p.1 + p.2.1) (p.1 + p.2.2.2) p.2.2.1
  | .interval => fun _ => 0

def HalflineReflectionIdentities (Q : Measure BridgeNoise) : Prop :=
  (∀ w y T z : ℝ, 0 < w → 0 < T → y < w → z < w →
    upperCompletion Q w y T z = Shao.C2.HalfLineReflectionFormula.upperReflection w y T z) ∧
  (∀ w y T z : ℝ, 0 < w → 0 < T → -w < y → -w < z →
    lowerCompletion Q w y T z = Shao.C2.HalfLineReflectionFormula.lowerReflection w y T z)

theorem actual_halfline_kernel_data
    (Q : Measure BridgeNoise) [IsProbabilityMeasure Q]
    (hReflection : HalflineReflectionIdentities Q)
    (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :
    Measurable (halflineDerivative J) ∧
    KernelBounds J (eventCompletionKernel J Q) (halflineDerivative J) 4 ∧
    (∀ w y T z : ℝ, 0 < w → 0 < T → Interior J w y → Interior J w z →
      HasDerivAt (fun s : ℝ => eventCompletionKernel J Q (w, s, T, z))
        (halflineDerivative J (w, y, T, z)) y) := by
  classical
  rcases hJ with rfl | rfl
  · have hm : Measurable (halflineDerivative .upper) := by
      change Measurable (fun p : ℝ × ℝ × ℝ × ℝ =>
        -Shao.C2.HalfLineMixedProfiles.slopeTime (p.1-p.2.1) (p.1-p.2.2.2) p.2.2.1)
      unfold Shao.C2.HalfLineMixedProfiles.slopeTime
      fun_prop
    refine ⟨hm, ⟨by norm_num, ?_, ?_⟩, ?_⟩
    · intro w y T z _ _ _ _
      exact (eventCompletionKernel_data .upper Q).2.1 (w,y,T,z)
    · intro w y T z hw hT hy hz
      have hu : 0 < w - y := sub_pos.mpr hy
      have hv : 0 < w - z := sub_pos.mpr hz
      have hb := Shao.C2.HalfLineReflectionFormula.positive_reflection_slope_bound
        (w-y) (w-z) T hu hv hT
      have he : (w-y)-(w-z) = z-y := by ring
      rw [he] at hb
      have hnn : 0 ≤ Shao.C2.HalfLineMixedProfiles.slopeTime (w-y) (w-z) T := by
        unfold Shao.C2.HalfLineMixedProfiles.slopeTime
        positivity
      change |-Shao.C2.HalfLineMixedProfiles.slopeTime (w-y) (w-z) T| ≤ _
      rw [abs_neg, abs_of_nonneg hnn]
      exact hb
    · intro w y T z hw hT hy hz
      have he := Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion_eq_scalar_of_reflection
        Q w z hw hz (fun S hS s hs => hReflection.1 w s S z hw hS hs hz)
      have hf : (fun s : ℝ => eventCompletionKernel .upper Q (w,s,T,z)) =
          (fun s : ℝ => Shao.C2.HalfLinePhysicalGaussian.upperCompletion w s T z) := by
        funext s
        have hh := congrFun (congrFun he s) T
        simpa only [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
          if_pos hw, if_pos hT, eventCompletionKernel] using hh
      rw [hf]
      exact Shao.C2.HalfLinePhysicalGaussian.upperCompletion_hasDerivAt w y T z hw hy hT hz
  · have hm : Measurable (halflineDerivative .lower) := by
      change Measurable (fun p : ℝ × ℝ × ℝ × ℝ =>
        Shao.C2.HalfLineMixedProfiles.slopeTime (p.1+p.2.1) (p.1+p.2.2.2) p.2.2.1)
      unfold Shao.C2.HalfLineMixedProfiles.slopeTime
      fun_prop
    refine ⟨hm, ⟨by norm_num, ?_, ?_⟩, ?_⟩
    · intro w y T z _ _ _ _
      exact (eventCompletionKernel_data .lower Q).2.1 (w,y,T,z)
    · intro w y T z hw hT hy hz
      have hu : 0 < w + y := by change -w < y at hy; linarith
      have hv : 0 < w + z := by change -w < z at hz; linarith
      have hb := Shao.C2.HalfLineReflectionFormula.positive_reflection_slope_bound
        (w+y) (w+z) T hu hv hT
      have he : (w+y)-(w+z) = y-z := by ring
      rw [he, abs_sub_comm y z] at hb
      have hnn : 0 ≤ Shao.C2.HalfLineMixedProfiles.slopeTime (w+y) (w+z) T := by
        unfold Shao.C2.HalfLineMixedProfiles.slopeTime
        positivity
      change |Shao.C2.HalfLineMixedProfiles.slopeTime (w+y) (w+z) T| ≤ _
      rw [abs_of_nonneg hnn]
      exact hb
    · intro w y T z hw hT hy hz
      have he := Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion_eq_scalar_of_reflection
        Q w z hw hz (fun S hS s hs => hReflection.2 w s S z hw hS hs hz)
      have hf : (fun s : ℝ => eventCompletionKernel .lower Q (w,s,T,z)) =
          (fun s : ℝ => Shao.C2.HalfLinePhysicalGaussian.lowerCompletion w s T z) := by
        funext s
        have hh := congrFun (congrFun he s) T
        simpa only [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
          if_pos hw, if_pos hT, eventCompletionKernel] using hh
      rw [hf]
      exact Shao.C2.HalfLinePhysicalGaussian.lowerCompletion_hasDerivAt w y T z hw hy hT hz

theorem actual_reveal_zero_future_reachable
    {n : ℕ} (a : Shao.Path n) (r : Fin n) (σ : LabelPerm n) :
    let y : ℝ := Shao.prefixSum (Spitzer.reorder a σ) r.val
    let T : ℝ := remainingEnergy a r.val σ
    let z : ℝ := Shao.prefixSum a n
    let b : ℝ := a (σ r)
    T - b ^ 2 = 0 → y + b = z := by
  classical
  intro y T z b hz
  have hf : Finset.univ.filter (fun i : Fin n => i.val < r.val + 1) =
      insert r (Finset.univ.filter (fun i : Fin n => i.val < r.val)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Fin.ext_iff]
    omega
  have hn : r ∉ Finset.univ.filter (fun i : Fin n => i.val < r.val) := by simp
  have hs : Shao.prefixSum (Spitzer.reorder a σ) (r.val + 1) = y + b := by
    unfold Shao.prefixSum
    rw [hf, Finset.sum_insert hn]
    change b + y = y + b
    ring
  have hq : Shao.prefixSquares (Spitzer.reorder a σ) (r.val + 1) =
      Shao.prefixSquares (Spitzer.reorder a σ) r.val + b ^ 2 := by
    unfold Shao.prefixSquares
    rw [hf, Finset.sum_insert hn]
    change b ^ 2 + Shao.prefixSquares (Spitzer.reorder a σ) r.val =
      Shao.prefixSquares (Spitzer.reorder a σ) r.val + b ^ 2
    ring
  have hfuture : remainingEnergy a (r.val + 1) σ = 0 := by
    dsimp only [T, remainingEnergy] at hz ⊢
    rw [hq]
    linarith only [hz]
  have hd := ((remaining_population_geometry a (r.val+1) (by omega) σ).2.2.2 hfuture).1
  change z - Shao.prefixSum (Spitzer.reorder a σ) (r.val+1) = 0 at hd
  rw [hs] at hd
  linarith only [hd]

theorem actual_halfline_retained_rank_domination
    {n : ℕ} (Q : Measure BridgeNoise) [IsProbabilityMeasure Q]
    (hReflection : HalflineReflectionIdentities Q)
    (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower)
    (a : Shao.Path n) (H x : ℝ) (hH : 0 < H) (hx : 0 < x)
    (ν : LabelPerm n → ℕ) (σ : LabelPerm n)
    (hcap : ν σ ≤ energyCutoff a H σ) (r : Fin n) :
    |sourceRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J)
      a x ν r.val σ| ≤
      8000100 * SourceIIDGaussianProfileBudget.rankGaussianWeight H x (wallSigns J) false
        (Spitzer.reorder a σ) r := by
  classical
  let w : ℝ := actualWall a x
  let y : ℝ := Shao.prefixSum (Spitzer.reorder a σ) r.val
  let T : ℝ := remainingEnergy a r.val σ
  let z : ℝ := Shao.prefixSum a n
  let b : ℝ := a (σ r)
  have hNN : 0 ≤ SourceIIDGaussianProfileBudget.rankGaussianWeight H x (wallSigns J) false
      (Spitzer.reorder a σ) r :=
    ((SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) H x (wallSigns J) false).2.1 _ _).1
  by_cases hact : r.val < ν σ ∧ sourceAlive J a x r.val σ ∧ 0 < T
  · have hw : 0 < w := mul_pos hx (Real.sqrt_pos.2 hact.2.1.1)
    have hy : Interior J w y := hact.2.1.2.2 r.val le_rfl
    have hz : Interior J w z := hact.2.1.2.1
    have hT : 0 < T := hact.2.2
    have hcut : H ≤ T := ((energy_cutoff_data a H hH).2.2 σ r.val
      (hact.1.trans_le hcap)).2
    have hb : b ^ 2 ≤ T := (remaining_population_geometry a r.val r.is_lt.le σ).2.2.1 r le_rfl
    have hzero : T - b ^ 2 = 0 → y + b = z := actual_reveal_zero_future_reachable a r σ
    have hqperm : Shao.energy (Spitzer.reorder a σ) = Shao.energy a := by
      simpa only [Shao.energy, Spitzer.reorder] using Equiv.sum_comp σ (fun i => (a i) ^ 2)
    have hsperm : Shao.prefixSum (Spitzer.reorder a σ) n = Shao.prefixSum a n := by
      simpa only [Shao.prefixSum_length, Spitzer.reorder] using Equiv.sum_comp σ a
    have hA : ∀ s ∈ wallSigns J,
        Shao.maxWithZero (s • Spitzer.head (Spitzer.reorder a σ) r.val r.is_lt.le) < w := by
      rcases hJ with rfl | rfl
      · intro s hs
        simp only [wallSigns, Finset.mem_singleton] at hs
        subst s
        unfold Shao.maxWithZero
        rw [Finset.sup'_lt_iff]
        intro k hk
        rw [Shao.prefixSum_smul, Spitzer.head_prefixSum _ _ _ k (Finset.mem_Icc.1 hk).2]
        have hh := hact.2.1.2.2 k (Finset.mem_Icc.1 hk).2
        change Shao.prefixSum (Spitzer.reorder a σ) k < w at hh
        simpa only [one_mul] using hh
      · intro s hs
        simp only [wallSigns, Finset.mem_singleton] at hs
        subst s
        unfold Shao.maxWithZero
        rw [Finset.sup'_lt_iff]
        intro k hk
        rw [Shao.prefixSum_smul, Spitzer.head_prefixSum _ _ _ k (Finset.mem_Icc.1 hk).2]
        have hh := hact.2.1.2.2 k (Finset.mem_Icc.1 hk).2
        change -w < Shao.prefixSum (Spitzer.reorder a σ) k at hh
        simp only [neg_one_mul]
        linarith only [hh]
    have hRank :
        SourceIIDGaussianProfileBudget.rankGaussianWeight H x (wallSigns J) false
          (Spitzer.reorder a σ) r =
        (|b| / Real.sqrt T) ^ 3 * (1 + |z-y| / Real.sqrt T) ^ 3 *
          (∑ s ∈ wallSigns J, Real.exp
            (-((max (w - s*y - (|b| + max (s*(z-y)) 0)) 0) ^ 2) / T)) := by
      have he := (SourceIIDGaussianProfileBudget.gaussian_weight_source_state
        (Spitzer.reorder a σ) r H x (wallSigns J) false).2.2.2.2
      rw [hqperm, hsperm] at he
      have hsel : 0 < Shao.energy a - Shao.prefixSquares (Spitzer.reorder a σ) r.val ∧
          H ≤ Shao.energy a - Shao.prefixSquares (Spitzer.reorder a σ) r.val ∧
          (∀ s ∈ wallSigns J,
            if false = true then Shao.maxWithZero
              (s • Spitzer.head (Spitzer.reorder a σ) r.val r.is_lt.le) ≤ x * Real.sqrt (Shao.energy a)
            else Shao.maxWithZero
              (s • Spitzer.head (Spitzer.reorder a σ) r.val r.is_lt.le) < x * Real.sqrt (Shao.energy a)) :=
        ⟨hT,hcut,by simpa only [Bool.false_eq_true, ite_false, w, actualWall] using hA⟩
      rw [if_pos hsel, if_pos (show 0 < Shao.energy a -
        Shao.prefixSquares (Spitzer.reorder a σ) r.val from hT)] at he
      exact he
    have hKernel := actual_halfline_kernel_data Q hReflection J hJ
    simp only [sourceRetainedRemainder, dif_pos r.is_lt,
      if_pos (show r.val < ν σ ∧ sourceAlive J a x r.val σ ∧
        0 < remainingEnergy a r.val σ from hact)]
    change |localRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J) w y T z b| ≤ _
    rcases hJ with rfl | rfl
    · change z < w at hz
      change y < w at hy
      have hExt (Y S : ℝ) :
          completionExt .upper (eventCompletionKernel .upper Q) w Y S z =
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y S z := by
        by_cases hY : Y < w
        · simp [completionExt, Interior,
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
            hw, hY, hz, eventCompletionKernel]
        · rw [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion_exterior Q w Y S z
            (by tauto)]
          simp [completionExt, Interior, hY]
      have hDer : deriv (fun Y : ℝ =>
          Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y T z) y =
          halflineDerivative .upper (w,y,T,z) := by
        have hf : (fun Y : ℝ =>
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y T z) =
            (fun Y : ℝ => eventCompletionKernel .upper Q (w,Y,T,z)) := by
          funext Y
          simp only [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
            if_pos hw, if_pos hT, eventCompletionKernel]
        rw [hf]
        exact (hKernel.2.2 w y T z hw hT hy hz).deriv
      have hRem (β : ℝ) :
          localRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
            w y T z β =
          Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w (y+β) (T-β^2) z -
            Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w y T z -
            (β-β^2*(z-y)/T) * deriv (fun Y : ℝ =>
              Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion Q w Y T z) y := by
        unfold localRemainder
        rw [hExt, hDer]
        simp only [Shao.C2.SourceHalfLineCompletion.sourceUpperCompletion,
          if_pos hw, if_pos hT, eventCompletionKernel, compensationCoefficient]
      have hbound := Shao.C2.SourceHalfLineCompletion.actual_upper_retained_bound_of_reflection
        Q w y T z b hw hy hz hT hb hzero
          (fun S hS Y hY => hReflection.1 w Y S z hw hS hY hz)
      dsimp only at hbound
      have hRet :
          localRetainedRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
            w y T z b =
          (if b^2 ≤ T/2 ∧ w ≤ y+b then
            localRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
              w y T z (w-y)
            else localRemainder .upper (eventCompletionKernel .upper Q) (halflineDerivative .upper)
              w y T z b) := by
        by_cases hs : b^2 ≤ T/2 <;> by_cases hc : w ≤ y+b <;>
          simp only [localRetainedRemainder, projectionIncrement, hT, hs, hc,
            true_and, and_self, and_false, and_true, if_true, if_false]
      rw [hRet]
      simp only [hRem] at *
      simp only [wallSigns, Finset.sum_singleton, one_mul] at hRank
      simp only [wallSigns] at ⊢
      rw [hRank]
      simpa only [mul_assoc] using hbound
    · change -w < z at hz
      change -w < y at hy
      have hExt (Y S : ℝ) :
          completionExt .lower (eventCompletionKernel .lower Q) w Y S z =
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y S z := by
        by_cases hY : -w < Y
        · simp [completionExt, Interior,
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
            hw, hY, hz, eventCompletionKernel]
        · rw [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion_exterior Q w Y S z
            (by tauto)]
          simp [completionExt, Interior, hY]
      have hDer : deriv (fun Y : ℝ =>
          Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y T z) y =
          halflineDerivative .lower (w,y,T,z) := by
        have hf : (fun Y : ℝ =>
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y T z) =
            (fun Y : ℝ => eventCompletionKernel .lower Q (w,Y,T,z)) := by
          funext Y
          simp only [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
            if_pos hw, if_pos hT, eventCompletionKernel]
        rw [hf]
        exact (hKernel.2.2 w y T z hw hT hy hz).deriv
      have hRem (β : ℝ) :
          localRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
            w y T z β =
          Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w (y+β) (T-β^2) z -
            Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w y T z -
            (β-β^2*(z-y)/T) * deriv (fun Y : ℝ =>
              Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion Q w Y T z) y := by
        unfold localRemainder
        rw [hExt, hDer]
        simp only [Shao.C2.SourceHalfLineCompletion.sourceLowerCompletion,
          if_pos hw, if_pos hT, eventCompletionKernel, compensationCoefficient]
      have hbound := Shao.C2.SourceHalfLineCompletion.actual_lower_retained_bound_of_reflection
        Q w y T z b hw hy hz hT hb hzero
          (fun S hS Y hY => hReflection.2 w Y S z hw hS hY hz)
      dsimp only at hbound
      have hRet :
          localRetainedRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
            w y T z b =
          (if b^2 ≤ T/2 ∧ y+b ≤ -w then
            localRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
              w y T z (-w-y)
            else localRemainder .lower (eventCompletionKernel .lower Q) (halflineDerivative .lower)
              w y T z b) := by
        by_cases hs : b^2 ≤ T/2 <;> by_cases hc : y+b ≤ -w <;>
          simp only [localRetainedRemainder, projectionIncrement, hT, hs, hc,
            true_and, and_self, and_false, and_true, if_true, if_false]
      rw [hRet]
      simp only [hRem] at *
      simp only [wallSigns, Finset.sum_singleton, neg_one_mul, sub_neg_eq_add, neg_sub] at hRank
      simp only [wallSigns] at ⊢
      rw [hRank]
      simpa only [mul_assoc] using hbound
  · have hinactive : ¬ (r.val < ν σ ∧ sourceAlive J a x r.val σ ∧
        0 < remainingEnergy a r.val σ) := hact
    rw [sourceRetainedRemainder, dif_pos r.is_lt, if_neg hinactive, abs_zero]
    exact mul_nonneg (by norm_num : (0 : ℝ) ≤ 8000100) hNN



theorem actual_energy_cutoff_measurable
    {n : ℕ} (H : ℝ) (hH : 0 < H) (σ : LabelPerm n) :
    Measurable (fun a : Shao.Path n => energyCutoff a H σ) := by
  classical
  apply measurable_of_Iic
  intro k
  by_cases hk : k ≤ n
  · have he : (fun a : Shao.Path n => energyCutoff a H σ) ⁻¹' Set.Iic k =
        {a | remainingEnergy a k σ < H} := by
      ext a
      exact (energy_cutoff_data a H hH).2.1 σ k hk
    rw [he]
    have hσ : Measurable (fun a : Shao.Path n => Spitzer.reorder a σ) :=
      Measurable.of_eval (fun i => measurable_pi_apply (σ i))
    exact measurableSet_lt
      (Shao.measurable_energy.sub ((Shao.measurable_prefixSquares k).comp hσ)) measurable_const
  · have he : (fun a : Shao.Path n => energyCutoff a H σ) ⁻¹' Set.Iic k = Set.univ := by
      ext a
      simp only [Set.mem_preimage, Set.mem_Iic, Set.mem_univ, iff_true]
      exact ((energy_cutoff_data a H hH).1.1 σ).trans (by omega)
    rw [he]
    exact MeasurableSet.univ

theorem iid_halfline_retained_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Measure BridgeNoise) [IsProbabilityMeasure Q],
        HalflineReflectionIdentities Q →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          ∀ (x : ℝ), 0 < x → x ≤ 1 →
            ∀ (ν : Shao.Path n → LabelPerm n → ℕ),
              (∀ σ, Measurable (fun a => ν a σ)) →
              (∀ a σ, ν a σ ≤ energyCutoff a h σ) →
              ∀ (J : MonitoredDomain), J = .upper ∨ J = .lower →
                let L : (Shao.Path n × LabelPerm n) → ℕ → ℝ := fun p r =>
                  sourceRetainedRemainder J (eventCompletionKernel J Q) (halflineDerivative J)
                    p.1 x (ν p.1) r p.2
                (∀ r : ℕ, Integrable (fun p => L p r) (revealLaw P)) ∧
                Integrable (fun p => ∑ r ∈ Finset.range n, |L p r|) (revealLaw P) ∧
                (∫ p, ∑ r ∈ Finset.range n, |L p r| ∂revealLaw P) ≤ C * R := by
  classical
  obtain ⟨CG, hCG, hGaussian⟩ :=
    SourceIIDGaussianProfileBudget.iid_gaussian_profile_early_late_budget
  refine ⟨8000100 * CG, by positivity, ?_⟩
  intro Q hQ hReflection nu hnu n hn h2 hmean hsecond
    sigmaSq scale normalizedLaw R h P x hx hx1 ν hνm hcap J hJ L
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure nu := hnu
  letI : IsProbabilityMeasure P := by dsimp [P]; infer_instance
  have hh : 0 < h :=
    (Shao.Probability.raw_truncation_budget_suffix_geometry nu n hn h2 hsecond).2.2.2.1
  have hKernel := actual_halfline_kernel_data Q hReflection J hJ
  have hParts := source_parts_measurable_integrable J (eventCompletionKernel J Q)
    (halflineDerivative J) (eventCompletionKernel_data J Q).1 hKernel.1
    4 hKernel.2.1 P x hx ν hνm
  have hLi (r : ℕ) : Integrable (fun p => L p r) (revealLaw P) := (hParts.2.1 r).1
  have hSi : Integrable (fun p => ∑ r ∈ Finset.range n, |L p r|) (revealLaw P) :=
    integrable_finsetSum _ (fun r _ => (hLi r).abs)
  have hsigns : ∀ s ∈ wallSigns J, s = 1 ∨ s = -1 := by
    rcases hJ with rfl | rfl <;> intro s hs
    · exact Or.inl (by simpa only [wallSigns, Finset.mem_singleton] using hs)
    · exact Or.inr (by simpa only [wallSigns, Finset.mem_singleton] using hs)
  have hGbudget := hGaussian nu n hn h2 hmean hsecond x hx hx1
    (wallSigns J) hsigns false
  let G : Shao.Path n → ℝ := fun a => ∑ r : Fin n,
    SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns J) false a r
  have hGi : Integrable G P := hGbudget.2.2.2.1
  have hGle : (∫ a, G a ∂P) ≤ CG * R := hGbudget.2.2.2.2.2.2
  have hRankMeas (r : Fin n) : Measurable (fun a : Shao.Path n =>
      SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns J) false a r) := by
    have hs : Measurable (fun a : Shao.Path n =>
        (Spitzer.head a r.val r.is_lt.le, Spitzer.tail a r.val r.is_lt.le)) :=
      (Measurable.of_eval fun i => measurable_pi_apply _).prodMk
        (Measurable.of_eval fun i => measurable_pi_apply _)
    exact (SourceIIDGaussianProfileBudget.fixed_gaussian_weight_measurable_bound
      r.val (n-r.val) h x (wallSigns J) false).1.comp hs
  have hGm : Measurable G := Finset.measurable_sum _ (fun r _ => hRankMeas r)
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P nu := by
    refine ⟨(hX i).aemeasurable, measurable_id.aemeasurable, ?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => nu) i).map_eq
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ)) (fun _ => measurable_id.aemeasurable)
  have hMap : Measure.map (fun p : Shao.Path n × LabelPerm n =>
      Spitzer.reorder p.1 p.2) (revealLaw P) = P :=
    iid_randomPermutation_map_eq_pi P nu X hX hIndep hLaw
  have hRm : Measurable (fun p : Shao.Path n × LabelPerm n =>
      Spitzer.reorder p.1 p.2) := by
    apply measurable_from_prod_countable_left
    intro σ
    exact Measurable.of_eval (fun i => measurable_pi_apply (σ i))
  have hPath : IdentDistrib (fun p : Shao.Path n × LabelPerm n =>
      Spitzer.reorder p.1 p.2) (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hRm.aemeasurable, measurable_id.aemeasurable, by simpa only [Measure.map_id] using hMap⟩
  have hGid := hPath.comp hGm
  have hReorderedGi : Integrable (fun p : Shao.Path n × LabelPerm n =>
      G (Spitzer.reorder p.1 p.2)) (revealLaw P) := hGid.integrable_iff.mpr hGi
  have hDom (p : Shao.Path n × LabelPerm n) :
      (∑ r ∈ Finset.range n, |L p r|) ≤
        8000100 * G (Spitzer.reorder p.1 p.2) := by
    rw [← Fin.sum_univ_eq_sum_range (fun r : ℕ => |L p r|) n]
    calc
      _ ≤ ∑ r : Fin n, 8000100 *
          SourceIIDGaussianProfileBudget.rankGaussianWeight h x (wallSigns J) false
            (Spitzer.reorder p.1 p.2) r :=
        Finset.sum_le_sum (fun r _ => actual_halfline_retained_rank_domination
          Q hReflection J hJ p.1 h x hh hx (ν p.1) p.2 (hcap p.1 p.2) r)
      _ = _ := by simp only [G, Finset.mul_sum]
  refine ⟨hLi, hSi, ?_⟩
  calc
    _ ≤ ∫ p, 8000100 * G (Spitzer.reorder p.1 p.2) ∂revealLaw P :=
      integral_mono hSi (hReorderedGi.const_mul 8000100) hDom
    _ = 8000100 * ∫ a, G a ∂P := by
      rw [integral_const_mul]
      exact congrArg (fun v : ℝ => 8000100 * v) hGid.integral_eq
    _ ≤ 8000100 * (CG * R) := mul_le_mul_of_nonneg_left hGle (by norm_num)
    _ = _ := by ring


theorem iid_actual_cutoff_two_halfline_budget :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : Measure BridgeNoise) [IsProbabilityMeasure Q],
        HalflineReflectionIdentities Q →
        ∀ (nu : Measure ℝ) [IsProbabilityMeasure nu] (n : ℕ) (hn : 0 < n),
          Integrable (fun z : ℝ => z ^ 2) nu →
          (∫ z : ℝ, z ∂nu) = 0 → 0 < (∫ z : ℝ, z ^ 2 ∂nu) →
          let sigmaSq : ℝ := ∫ z : ℝ, z ^ 2 ∂nu
          let scale : ℝ := Real.sqrt ((n : ℝ) * sigmaSq)
          let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z / scale) nu
          let R : ℝ := Shao.truncationBudget normalizedLaw n 0
          let h : ℝ := 4 * (n : ℝ) * sigmaSq * R ^ 2
          let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => nu)
          let ν : Shao.Path n → LabelPerm n → ℕ := fun a σ => energyCutoff a h σ
          ∀ (x : ℝ), 0 < x → x ≤ 1 →
            let L : MonitoredDomain → (Shao.Path n × LabelPerm n) → ℕ → ℝ :=
              fun J p r => sourceRetainedRemainder J (eventCompletionKernel J Q)
                (halflineDerivative J) p.1 x (ν p.1) r p.2
            (∀ J : MonitoredDomain, J = .upper ∨ J = .lower →
              Integrable (fun p => ∑ r ∈ Finset.range n, |L J p r|) (revealLaw P)) ∧
            ((∫ p, ∑ r ∈ Finset.range n, |L .upper p r| ∂revealLaw P) +
              (∫ p, ∑ r ∈ Finset.range n, |L .lower p r| ∂revealLaw P)) ≤ C * R := by
  classical
  obtain ⟨C, hC, hHalfline⟩ := iid_halfline_retained_budget
  refine ⟨2 * C, by positivity, ?_⟩
  intro Q hQ hReflection nu hnu n hn h2 hmean hsecond
    sigmaSq scale normalizedLaw R h P ν x hx hx1 L
  letI : IsProbabilityMeasure Q := hQ
  letI : IsProbabilityMeasure nu := hnu
  have hh : 0 < h :=
    (Shao.Probability.raw_truncation_budget_suffix_geometry nu n hn h2 hsecond).2.2.2.1
  have hνm (σ : LabelPerm n) : Measurable (fun a => ν a σ) :=
    actual_energy_cutoff_measurable h hh σ
  have hcap (a : Shao.Path n) (σ : LabelPerm n) : ν a σ ≤ energyCutoff a h σ := le_rfl
  have hJ (J : MonitoredDomain) (hJ : J = .upper ∨ J = .lower) :=
    hHalfline Q hReflection nu n hn h2 hmean hsecond x hx hx1 ν hνm hcap J hJ
  refine ⟨fun J hhalf => (hJ J hhalf).2.1, ?_⟩
  have hU := (hJ .upper (Or.inl rfl)).2.2
  have hL := (hJ .lower (Or.inr rfl)).2.2
  calc
    _ ≤ C * R + C * R := add_le_add hU hL
    _ = _ := by ring


end Shao.Probability.SourceActualLocalProfileBudget
