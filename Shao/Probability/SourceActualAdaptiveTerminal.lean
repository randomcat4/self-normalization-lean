/- Mathematical candidate only. SourceWeightedPrefixWall is a frozen candidate
   dependency whose full formal qualification is still pending. No Lean body/check. -/
import Shao.Probability.SourceTerminalEnvelope
import Shao.Probability.SourcePermutationReveal
import Shao.Probability.SourceWeightedPrefixWall
import Shao.Probability.SourceTrueWallProfile
import Shao.Probability.QuadraticEnergyLowerTail
import Shao.Probability.TruncationIntegrals
import Shao.Probability.SourceActualLocalProfileBudget
import Shao.C2.CompletionMeasurability
import Shao.C2.AuxiliaryEnergyCentered
import Shao.C2.AuxiliaryLowEnergyGaussian
import Mathlib.MeasureTheory.Integral.Prod

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 5000000
noncomputable section
namespace Shao.Probability.SourceActualAdaptiveTerminal
open MeasureTheory ProbabilityTheory
open SourcePermutationReveal
open Shao.C2.BridgeDomination Shao.C2.BrownianBridgeLaw
open scoped BigOperators Classical NNReal

local instance labelPermMeasurableSpace (n : ℕ) : MeasurableSpace (LabelPerm n) := ⊤

private theorem aat_actual_fixed_suffix_terminal_budget :
    ∃ CF : ℝ, 0 < CF ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (cap : ℝ), 0 < cap → (∀ᵐ z : ℝ ∂rho, |z| ≤ cap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          ∀ r t : ℕ, 0 < r → t ≤ r →
            let n : ℕ := r + t
            ∀ x : ℝ, 1 ≤ x → cap ≤ Real.sqrt (n : ℝ) / (200 * x) →
              ∀ (I : MonitoredDomain) (b : Shao.Path t),
                let Pprefix : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rho)
                let F : BridgeKernel := eventCompletionKernel I (bridgeLaw B PB)
                let U : ℝ := Shao.energy b
                let J : ℝ := (Finset.Icc 0 t).sup'
                  (by exact ⟨0, Finset.mem_Icc.mpr ⟨le_rfl, Nat.zero_le _⟩⟩)
                  (fun l => |Shao.prefixSum b l|)
                let a : Shao.Path r → Shao.Path n := fun v => Fin.append v b
                let terminal : Shao.Path r → ℝ := fun v =>
                  if sourceAlive I (a v) x n (Equiv.refl (Fin n)) then 1 else 0
                let discrepancy : Shao.Path r → ℝ := fun v =>
                  (Finset.Icc r n).sup'
                    (by exact ⟨r, Finset.mem_Icc.mpr
                      ⟨le_rfl, Nat.le_add_right r t⟩⟩)
                    (fun j => |sourceValue I F (a v) x j (Equiv.refl (Fin n)) - terminal v|)
                Measurable discrepancy ∧ Integrable discrepancy Pprefix ∧
                  (∫ v, discrepancy v ∂Pprefix) ≤ CF * (J ^ 2 + U + beta ^ 2) / (r : ℝ) := by
  classical
  obtain ⟨CW, hCW, hWall⟩ :=
    SourceWeightedPrefixWall.actual_circular_weighted_true_wall_closed_cdf
  have hCW0 : 0<CW := by linarith
  refine ⟨1024 * (1 + CW), by positivity, ?_⟩
  intro Ω _ PB _ B hB rho hrho cap hcap0 hcapAE hmean hsecond beta r t hr htr n
    x hx hcap I b Pprefix F U J a terminal discrepancy
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure (bridgeLaw B PB) := isProbabilityMeasure_bridgeLaw B PB hB
  have hrR : 0 < (r : ℝ) := by exact_mod_cast hr
  have hrS : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.2 hrR
  have hn : 0 < n := by dsimp [n]; omega
  have hrn : r ≤ n := Nat.le_add_right r t
  have hnHalf : (n : ℝ) / 2 ≤ (r : ℝ) := by
    have hh : (t : ℝ) ≤ (r : ℝ) := by exact_mod_cast htr
    dsimp [n]
    push_cast
    linarith
  have h2 : Integrable (fun z : ℝ => z ^ 2) rho := by
    apply Integrable.of_bound (by fun_prop) (cap ^ 2)
    filter_upwards [hcapAE] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg z), ← sq_abs z]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z| ^ 3) rho := by
    apply Integrable.of_bound (by fun_prop) (cap ^ 3)
    filter_upwards [hcapAE] with z hz
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (abs_nonneg z) 3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hBeta : 1 ≤ beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one
      rho h2 h3 hsecond
  have hBeta0 : 0 < beta := by linarith
  have hU0 : 0 ≤ U := Shao.energy_nonneg b
  have hJ0 : 0 ≤ J :=
    (abs_nonneg (Shao.prefixSum b 0)).trans
      (Finset.le_sup' (fun l => |Shao.prefixSum b l|)
        (Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le t⟩))
  have haM : Measurable a := by
    apply Measurable.of_eval
    intro i
    refine Fin.addCases ?_ ?_ i
    · intro j
      simpa only [a, Fin.append_left] using
        (measurable_pi_apply j : Measurable (fun v : Shao.Path r => v j))
    · intro j
      simpa only [a, Fin.append_right] using
        (measurable_const : Measurable (fun _ : Shao.Path r => b j))
  have hAppend (v : Shao.Path r) :
      Shao.energy (a v) = Shao.energy v + U ∧
      Shao.prefixSquares (a v) r = Shao.energy v ∧
      (∀ k : ℕ, k ≤ r → Shao.prefixSum (a v) k = Shao.prefixSum v k) ∧
      ∀ l : ℕ, Shao.prefixSum (a v) (r + l) - Shao.prefixSum (a v) r =
        Shao.prefixSum b l := by
    have he : Shao.energy (a v) = Shao.energy v + U := by
      dsimp only [a, U]
      unfold Shao.energy
      rw [Fin.sum_univ_add]
      simp only [Fin.append_left, Fin.append_right]
    have hq : Shao.prefixSquares (a v) r = Shao.energy v := by
      rw [Shao.prefixSquares, Finset.sum_filter, Fin.sum_univ_add]
      have hl (i : Fin r) : i.val < r := i.is_lt
      have ht' (i : Fin t) : ¬r + i.val < r := by omega
      simp [a, hl, ht', Shao.energy]
    have hh : Spitzer.head (a v) r hrn = v := by
      ext i
      exact Fin.append_left _ _ _
    have hp (k : ℕ) (hk : k ≤ r) : Shao.prefixSum (a v) k = Shao.prefixSum v k := by
      have h := Spitzer.head_prefixSum (a v) r hrn k hk
      rw [hh] at h
      exact h.symm
    refine ⟨he, hq, hp, ?_⟩
    intro l
    rw [Shao.OQ4.prefixSum_append, hp r le_rfl]
    ring
  have hRemaining (v : Shao.Path r) :
      remainingEnergy (a v) r (Equiv.refl (Fin n)) = U := by
    change Shao.energy (a v) - Shao.prefixSquares (a v) r = U
    rw [(hAppend v).1, (hAppend v).2.1]
    ring
  have hSuffixMax (v : Shao.Path r) :
      (Finset.Icc 0 (n-r)).sup'
        (by exact ⟨0, Finset.mem_Icc.2 ⟨le_rfl, Nat.zero_le _⟩⟩)
        (fun l => |Shao.prefixSum (a v) (r+l)-Shao.prefixSum (a v) r|) = J := by
    have hlen : n-r=t := by dsimp [n]; omega
    simp only [hlen, (hAppend v).2.2.2]
    rfl
  have hF : Measurable F := by
    cases I with
    | upper => exact Shao.C2.CompletionMeasurability.measurable_upperCompletion_parameters _
    | lower => exact Shao.C2.CompletionMeasurability.measurable_lowerCompletion_parameters _
    | interval => exact Shao.C2.CompletionMeasurability.measurable_intervalCompletion_parameters _
  have hwM : Measurable (fun v : Shao.Path r => actualWall (a v) x) :=
    measurable_const.mul ((Shao.measurable_energy.comp haM).sqrt)
  have hIntM (g : Shao.Path r → ℝ) (hg : Measurable g) :
      MeasurableSet {v | Interior I (actualWall (a v) x) (g v)} := by
    cases I with
    | upper => exact measurableSet_lt hg hwM
    | lower => exact measurableSet_lt hwM.neg hg
    | interval => exact (measurableSet_lt hwM.neg hg).inter (measurableSet_lt hg hwM)
  have hAliveM (j : ℕ) :
      MeasurableSet {v : Shao.Path r | sourceAlive I (a v) x j (Equiv.refl (Fin n))} := by
    have hp : MeasurableSet {v : Shao.Path r | ∀ k : ℕ, k ≤ j →
        Interior I (actualWall (a v) x) (Shao.prefixSum (a v) k)} := by
      rw [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro k
      by_cases hk : k ≤ j
      · simpa only [hk, true_implies, Function.comp_def] using
          hIntM _ ((Shao.measurable_prefixSum k).comp haM)
      · simp only [hk, false_implies, Set.setOf_true, MeasurableSet.univ]
    exact (measurableSet_lt measurable_const (Shao.measurable_energy.comp haM)).inter
      ((hIntM _ ((Shao.measurable_prefixSum n).comp haM)).inter hp)
  have hSM (j : ℕ) : Measurable (fun v : Shao.Path r =>
      sourceValue I F (a v) x j (Equiv.refl (Fin n))) := by
    have hy : Measurable (fun v : Shao.Path r => Shao.prefixSum (a v) j) :=
      (Shao.measurable_prefixSum j).comp haM
    have hz : Measurable (fun v : Shao.Path r => Shao.prefixSum (a v) n) :=
      (Shao.measurable_prefixSum n).comp haM
    have hT : Measurable (fun v : Shao.Path r =>
        remainingEnergy (a v) j (Equiv.refl (Fin n))) :=
      (Shao.measurable_energy.sub (Shao.measurable_prefixSquares j)).comp haM
    have hGuard : MeasurableSet {v : Shao.Path r |
        0 < actualWall (a v) x ∧
        Interior I (actualWall (a v) x) (Shao.prefixSum (a v) j) ∧
        Interior I (actualWall (a v) x) (Shao.prefixSum (a v) n)} :=
      (measurableSet_lt measurable_const hwM).inter ((hIntM _ hy).inter (hIntM _ hz))
    unfold sourceValue completionExt
    exact Measurable.ite (hAliveM j)
      (Measurable.ite hGuard
        (Measurable.ite (measurableSet_lt measurable_const hT)
          (hF.comp (hwM.prodMk (hy.prodMk (hT.prodMk hz))))
          (Measurable.ite
            ((measurableSet_eq_fun hT measurable_const).inter (measurableSet_eq_fun hy hz))
            measurable_const measurable_const)) measurable_const) measurable_const
  have htM : Measurable terminal :=
    Measurable.ite (hAliveM n) measurable_const measurable_const
  have hDM : Measurable discrepancy := by
    have hf (j : ℕ) (hj : j ∈ Finset.Icc r n) : Measurable
        (fun v : Shao.Path r => |sourceValue I F (a v) x j (Equiv.refl (Fin n)) - terminal v|) :=
      continuous_abs.measurable.comp ((hSM j).sub htM)
    convert Finset.measurable_sup' (s := Finset.Icc r n)
      (by exact ⟨r, Finset.mem_Icc.2 ⟨le_rfl, hrn⟩⟩) hf using 1
    ext v
    exact (Finset.sup'_apply
      (by exact ⟨r, Finset.mem_Icc.2 ⟨le_rfl, hrn⟩⟩)
      (fun (j : ℕ) (v : Shao.Path r) =>
        |sourceValue I F (a v) x j (Equiv.refl (Fin n)) - terminal v|) v).symm
  have hCorr (v : Shao.Path r) :=
    actual_source_terminal_corridor_envelope PB B hB n (a v) r hrn x (by linarith) I
  have hD0 (v : Shao.Path r) : 0 ≤ discrepancy v := (hCorr v).1
  have hD1 (v : Shao.Path r) : discrepancy v ≤ 1 := (hCorr v).2.1
  have hDi : Integrable discrepancy Pprefix := by
    apply Integrable.of_bound hDM.aestronglyMeasurable 1
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hD0 v)]
      exact hD1 v
  refine ⟨hDM, hDi, ?_⟩
  by_cases hUz : U = 0
  · have hz (v : Shao.Path r) : discrepancy v = 0 :=
      (hCorr v).2.2.1 (by rw [hRemaining v, hUz])
    have hzero : (∫ v,discrepancy v ∂Pprefix)=0 := by
      calc
        _ =∫ _ : Shao.Path r,(0:ℝ) ∂Pprefix :=
          integral_congr_ae (ae_of_all _ hz)
        _ =0 := by simp
    rw [hzero]
    exact div_nonneg (mul_nonneg (by positivity)
      (add_nonneg (add_nonneg (sq_nonneg J) hU0) (sq_nonneg beta))) hrR.le
  have hU : 0 < U := lt_of_le_of_ne hU0 (Ne.symm hUz)
  let wall : Shao.Path r → ℝ := fun v => x * Real.sqrt (Shao.energy v + U)
  let gap : ℝ → Shao.Path r → ℝ := fun eta v => wall v - eta * Shao.prefixSum v r
  let A : ℝ → Set (Shao.Path r) := fun eta => {v | ∀ k : Fin (r+1),
    0 < k.val → eta * Shao.prefixSum v k.val < wall v}
  let G : Set (Shao.Path r) := {v | (r : ℝ)/2 ≤ Shao.energy v}
  have hwallM : Measurable wall :=
    measurable_const.mul ((Shao.measurable_energy.add_const U).sqrt)
  have hgapM (eta : ℝ) : Measurable (gap eta) :=
    hwallM.sub (measurable_const.mul (Shao.measurable_prefixSum r))
  have hAM (eta : ℝ) : MeasurableSet (A eta) := by
    change MeasurableSet {v : Shao.Path r | ∀ k : Fin (r+1),
      0 < k.val → eta * Shao.prefixSum v k.val < wall v}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro k
    by_cases hk : 0 < k.val
    · simpa only [hk, true_implies, Pi.mul_apply] using
        measurableSet_lt (measurable_const.mul (Shao.measurable_prefixSum k.val)) hwallM
    · simp only [hk, false_implies, Set.setOf_true, MeasurableSet.univ]
  have hGM : MeasurableSet G := measurableSet_le measurable_const Shao.measurable_energy
  have hgapPos (eta : ℝ) (v : Shao.Path r) (hv : v ∈ A eta) : 0 < gap eta v := by
    have hh := hv ⟨r, by omega⟩ hr
    dsimp [gap]
    linarith
  have hCDF (eta : ℝ) (heta : eta = 1 ∨ eta = -1) (s : ℝ) (hs : 0 ≤ s) :
      Pprefix.real {v | v ∈ A eta ∩ G ∧ gap eta v ≤ s} ≤
        CW * (s + beta)^2 / (r : ℝ) := by
    let rhoS : Measure ℝ := Measure.map (fun z : ℝ => eta * z) rho
    let PS : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rhoS)
    let S : Shao.Path r → Shao.Path r := fun v => eta • v
    have hm : Measurable (fun z : ℝ => eta*z) := measurable_const.mul measurable_id
    letI : IsProbabilityMeasure rhoS := by dsimp [rhoS]; infer_instance
    have habs (z : ℝ) : |eta*z|=|z| := by
      rcases heta with rfl | rfl <;> simp
    have hsq (z : ℝ) : (eta*z)^2=z^2 := by
      rcases heta with rfl | rfl <;> ring
    have hcaps : ∀ᵐ z : ℝ ∂rhoS, |z| ≤ cap := by
      apply (ae_map_iff hm.aemeasurable
        (measurableSet_le continuous_abs.measurable measurable_const)).2
      simpa only [habs] using hcapAE
    have hmeans : (∫ z : ℝ, z ∂rhoS)=0 := by
      rw [show rhoS=Measure.map (fun z : ℝ => eta*z) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => z) (by fun_prop),
        integral_const_mul, hmean, mul_zero]
    have hseconds : (∫ z : ℝ, z^2 ∂rhoS)=1 := by
      rw [show rhoS=Measure.map (fun z : ℝ => eta*z) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => z^2) (by fun_prop)]
      simpa only [hsq] using hsecond
    have hbetas : (∫ z : ℝ, |z|^3 ∂rhoS)=beta := by
      rw [show rhoS=Measure.map (fun z : ℝ => eta*z) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => |z|^3) (by fun_prop)]
      simp only [habs]
      rfl
    let wallS : Shao.Path r → ℝ := fun v => x*Real.sqrt (Shao.energy v+U)
    let gapS : Shao.Path r → ℝ := fun v => wallS v-Shao.prefixSum v r
    let AS : Set (Shao.Path r) := {v | ∀ k : Fin (r+1),
      0 < k.val → Shao.prefixSum v k.val < wallS v}
    let ES : Set (Shao.Path r) := AS ∩ G ∩ {v | 0<gapS v ∧ gapS v≤s}
    have hASM : MeasurableSet AS := by simpa only [A, one_mul] using hAM 1
    have hgapSM : Measurable gapS := hwallM.sub (Shao.measurable_prefixSum r)
    have hESM : MeasurableSet ES :=
      (hASM.inter hGM).inter
        ((measurableSet_lt measurable_const hgapSM).inter
          (measurableSet_le hgapSM measurable_const))
    have hb := hWall rhoS cap hcap0 hcaps hmeans hseconds n hn x hx hcap
      r hrn hnHalf U hU0 0 s (by norm_num) (by positivity) hs
    have hprob : PS.real ES ≤ CW*(s+beta)^2/(r : ℝ) := by
      have hb0 : (∫ v,ES.indicator (fun _ => (1:ℝ)) v ∂PS)≤CW*(s+beta)^2/(r : ℝ) := by
        simpa only [hbetas,zero_pow (by decide : (2:ℕ)≠0),
          zero_pow (by decide : (3:ℕ)≠0),zero_mul,mul_zero,zero_add,add_zero,
          one_pow,Real.exp_zero,mul_one,ES,AS,gapS,wallS,G] using hb.2
      have hone : (∫ v,ES.indicator (fun _ => (1:ℝ)) v ∂PS)=PS.real ES := by
        change (∫ v,ES.indicator 1 v ∂PS)=PS.real ES
        exact integral_indicator_one hESM
      rwa [hone] at hb0
    have hSM : Measurable S :=
      Measurable.of_eval fun i => measurable_const.mul (measurable_pi_apply i)
    have hmap : Measure.map S Pprefix=PS :=
      Measure.pi_map_pi (fun _ : Fin r => hm.aemeasurable)
    have henergyS (v : Shao.Path r) : Shao.energy (S v)=Shao.energy v := by
      rw [Shao.energy_smul]
      rcases heta with rfl | rfl <;> norm_num
    have hevent : S ⁻¹' ES={v | v∈A eta∩G ∧ gap eta v≤s} := by
      ext v
      simp only [Set.mem_preimage, ES, Set.mem_inter_iff, Set.mem_setOf_eq,
        AS, wallS, gapS, henergyS, S, Shao.prefixSum_smul, A, G, wall, gap]
      constructor
      · rintro ⟨⟨ha,hg⟩,hw⟩
        exact ⟨⟨ha,hg⟩,hw.2⟩
      · rintro ⟨⟨ha,hg⟩,hw⟩
        exact ⟨⟨ha,hg⟩,hgapPos eta v ha,hw⟩
    rw [←hmap, Measure.real_def, Measure.map_apply hSM hESM, hevent] at hprob
    exact hprob
  have hProfile (eta : ℝ) (heta : eta=1 ∨ eta= -1) :
      Integrable ((A eta∩G).indicator
        (fun v => Real.exp (-((gap eta v)^2)/(32*U)))) Pprefix ∧
      (∫ v, (A eta∩G).indicator
        (fun v => Real.exp (-((gap eta v)^2)/(32*U))) v ∂Pprefix) ≤
          128*CW*U/(r : ℝ)+2*CW*beta^2/(r : ℝ) := by
    let profile : Shao.Path r → ℝ := fun v =>
      Real.exp (-((max (gap eta v-0) 0)^2)/(32*U))
    have heq : (A eta∩G).indicator profile =
        (A eta∩G).indicator (fun v => Real.exp (-((gap eta v)^2)/(32*U))) := by
      ext v
      by_cases hv : v∈A eta∩G
      · simp only [Set.indicator_of_mem hv, profile, sub_zero,
          max_eq_left (hgapPos eta v hv.1).le]
      · simp only [Set.indicator_of_notMem hv]
    have hQuad (s : ℝ) (hs : 0≤s) :
        Pprefix.real {v | v∈A eta∩G ∧ gap eta v≤s} ≤
          (2*CW)*(s^2/(r : ℝ)+(beta/Real.sqrt (r : ℝ))^2) := by
      have hh := hCDF eta heta s hs
      have hrat : (s+beta)^2/(r : ℝ) ≤
          2*(s^2/(r : ℝ)+(beta/Real.sqrt (r : ℝ))^2) := by
        rw [div_pow, Real.sq_sqrt hrR.le]
        have hnum : (s+beta)^2≤2*(s^2+beta^2) := by nlinarith [sq_nonneg (s-beta)]
        have hh := div_le_div_of_nonneg_right hnum hrR.le
        convert hh using 1 <;> ring
      apply hh.trans
      calc
        CW*(s+beta)^2/(r : ℝ)=CW*((s+beta)^2/(r : ℝ)) := by ring
        _ ≤CW*(2*(s^2/(r : ℝ)+(beta/Real.sqrt (r : ℝ))^2)) :=
          mul_le_mul_of_nonneg_left hrat hCW0.le
        _ =_ := by ring
    have hi := (gaussian_wall_profile_layer_cake Pprefix (A eta∩G)
      ((hAM eta).inter hGM) (gap eta) (hgapM eta) (32*U) 0
      (by positivity) (by norm_num)).1
    have hb := gaussian_wall_profile_of_quadratic_closed_cdf Pprefix (A eta∩G)
      ((hAM eta).inter hGM) (gap eta) (hgapM eta) (2*CW)
      (beta/Real.sqrt (r : ℝ)) (r : ℝ) (32*U) 0
      (by positivity) hrR (by positivity) (by norm_num) hQuad
    rw [heq] at hi hb
    refine ⟨hi, hb.trans_eq ?_⟩
    rw [zero_pow (by omega), zero_add, div_pow, Real.sq_sqrt hrR.le]
    ring
  let q : ℝ → Shao.Path r → ℝ := fun eta => (A eta∩G).indicator (fun v =>
    (if gap eta v≤2*J then 1 else 0)+2*Real.exp (-((gap eta v)^2)/(32*U)))
  have hqM (eta : ℝ) : Measurable (q eta) := by
    apply Measurable.indicator _ ((hAM eta).inter hGM)
    exact (Measurable.ite (measurableSet_le (hgapM eta) measurable_const)
      measurable_const measurable_const).add
      (measurable_const.mul (((hgapM eta).pow_const 2).neg.div_const (32*U)).exp)
  have hq0 (eta : ℝ) (v : Shao.Path r) : 0≤q eta v := by
    by_cases hv : v∈A eta∩G
    · rw [show q eta v=(A eta∩G).indicator
        (fun v => (if gap eta v≤2*J then 1 else 0)+2*Real.exp (-((gap eta v)^2)/(32*U))) v from rfl,
        Set.indicator_of_mem hv]
      split_ifs <;> positivity
    · rw [show q eta v=(A eta∩G).indicator
        (fun v => (if gap eta v≤2*J then 1 else 0)+2*Real.exp (-((gap eta v)^2)/(32*U))) v from rfl,
        Set.indicator_of_notMem hv]
  have hq3 (eta : ℝ) (v : Shao.Path r) : q eta v≤3 := by
    by_cases hv : v∈A eta∩G
    · have he : Real.exp (-((gap eta v)^2)/(32*U))≤1 :=
        Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _))
          (by positivity))
      dsimp only [q]
      rw [Set.indicator_of_mem hv]
      split_ifs <;> linarith [Real.exp_pos (-((gap eta v)^2)/(32*U))]
    · simp only [q, Set.indicator_of_notMem hv]
      norm_num
  have hqi (eta : ℝ) : Integrable (q eta) Pprefix := by
    apply Integrable.of_bound (hqM eta).aestronglyMeasurable 3
    exact ae_of_all _ fun v => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hq0 eta v)]
      exact hq3 eta v
  have hqb (eta : ℝ) (heta : eta=1 ∨ eta= -1) :
      (∫ v, q eta v ∂Pprefix) ≤
        CW*(8*J^2+256*U+6*beta^2)/(r : ℝ) := by
    let E : Set (Shao.Path r) := {v | v∈A eta∩G ∧ gap eta v≤2*J}
    have hEM : MeasurableSet E :=
      ((hAM eta).inter hGM).inter (measurableSet_le (hgapM eta) measurable_const)
    have hEint : Integrable (E.indicator (fun _ : Shao.Path r => (1:ℝ))) Pprefix :=
      integrable_const _ |>.indicator hEM
    have hEq : q eta = fun v => E.indicator (fun _ => (1:ℝ)) v+
        2*((A eta∩G).indicator
          (fun v => Real.exp (-((gap eta v)^2)/(32*U))) v) := by
      ext v
      by_cases hv : v∈A eta∩G
      · by_cases hw : gap eta v≤2*J
        · have he : v∈E := ⟨hv,hw⟩
          simp only [q,Set.indicator_of_mem hv,Set.indicator_of_mem he,if_pos hw]
        · have he : v∉E := fun hh => hw hh.2
          simp only [q,Set.indicator_of_mem hv,Set.indicator_of_notMem he,if_neg hw,zero_add]
      · have he : v∉E := fun hh => hv hh.1
        simp only [q,Set.indicator_of_notMem hv,Set.indicator_of_notMem he,mul_zero,add_zero]
    have hone : (∫ v,E.indicator (fun _ => (1:ℝ)) v ∂Pprefix)=Pprefix.real E := by
      change (∫ v,E.indicator 1 v ∂Pprefix)=_
      exact integral_indicator_one hEM
    rw [hEq,integral_add hEint ((hProfile eta heta).1.const_mul 2),integral_const_mul,hone]
    have hn := hCDF eta heta (2*J) (by positivity)
    have hg := (hProfile eta heta).2
    have hnear : CW*(2*J+beta)^2/(r : ℝ) ≤
        CW*(8*J^2+2*beta^2)/(r : ℝ) := by
      apply div_le_div_of_nonneg_right _ hrR.le
      apply mul_le_mul_of_nonneg_left _ (by linarith)
      nlinarith [sq_nonneg (2*J-beta)]
    calc
      Pprefix.real E+2*(∫ v, (A eta∩G).indicator
          (fun v => Real.exp (-((gap eta v)^2)/(32*U))) v ∂Pprefix)
        ≤ CW*(8*J^2+2*beta^2)/(r : ℝ)+
          2*(128*CW*U/(r : ℝ)+2*CW*beta^2/(r : ℝ)) :=
          add_le_add (hn.trans hnear) (mul_le_mul_of_nonneg_left hg (by norm_num))
      _ = _ := by ring
  have hLow : Pprefix.real Gᶜ ≤ 64*beta^2/(r : ℝ) := by
    let scale : ℝ := Real.sqrt (r : ℝ)
    let rhoR : Measure ℝ := Measure.map (fun z : ℝ => z/scale) rho
    let PR : Measure (Shao.Path r) := Measure.pi (fun _ : Fin r => rhoR)
    let S : Shao.Path r → Shao.Path r := fun v i => v i/scale
    have hs : 0<scale := hrS
    have hs2 : scale^2=(r : ℝ) := Real.sq_sqrt hrR.le
    have hm : Measurable (fun z : ℝ => z/scale) := measurable_id.div_const _
    letI : IsProbabilityMeasure rhoR := by dsimp [rhoR]; infer_instance
    have h2R : Integrable (fun z : ℝ => z^2) rhoR := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def,div_pow] using h2.div_const (scale^2)
    have h3R : Integrable (fun z : ℝ => |z|^3) rhoR := by
      apply (integrable_map_measure (by fun_prop) hm.aemeasurable).2
      simpa only [Function.comp_def,abs_div,abs_of_pos hs,div_pow] using
        h3.div_const (scale^3)
    have hNorm : (r : ℝ)*(∫ z : ℝ,z^2 ∂rhoR)=1 := by
      rw [show rhoR=Measure.map (fun z : ℝ => z/scale) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => z^2) (by fun_prop)]
      simp_rw [div_pow]
      rw [integral_div,hsecond,hs2]
      exact mul_one_div_cancel hrR.ne'
    have hBetaR : (r : ℝ)*(∫ z : ℝ,|z|^3 ∂rhoR)=beta/scale := by
      rw [show rhoR=Measure.map (fun z : ℝ => z/scale) rho from rfl,
        integral_map hm.aemeasurable (f := fun z : ℝ => |z|^3) (by fun_prop)]
      simp only [abs_div,abs_of_pos hs,div_pow]
      rw [integral_div]
      change (r : ℝ)*(beta/scale^3)=beta/scale
      field_simp
      nlinarith [hs2]
    have hTail := (finite_iid_energy_lower_tail rhoR r hr h2R h3R hNorm
      (1/2) (by norm_num) (by norm_num)).2
    rw [hBetaR] at hTail
    have hSM : Measurable S :=
      Measurable.of_eval fun i => by
        simpa only [S] using (measurable_pi_apply i : Measurable (fun v : Shao.Path r => v i)).div_const scale
    have hmap : Measure.map S Pprefix=PR :=
      Measure.pi_map_pi (fun _ : Fin r => hm.aemeasurable)
    have hES : MeasurableSet {v : Shao.Path r | Shao.energy v≤1-(1/2 : ℝ)} :=
      measurableSet_le Shao.measurable_energy measurable_const
    have he (v : Shao.Path r) : Shao.energy (S v)=Shao.energy v/(r : ℝ) := by
      simp only [S,Shao.energy,div_pow,hs2,Finset.sum_div]
    have hSet : S ⁻¹' {v : Shao.Path r | Shao.energy v≤1-(1/2 : ℝ)}=
        {v : Shao.Path r | Shao.energy v≤(r : ℝ)/2} := by
      ext v
      simp only [Set.mem_preimage,Set.mem_setOf_eq,he,div_le_iff₀ hrR]
      constructor <;> intro hh <;> linarith
    change PR.real {v : Shao.Path r | Shao.energy v≤1-(1/2 : ℝ)}≤_ at hTail
    rw [←hmap,Measure.real_def,Measure.map_apply hSM hES,hSet] at hTail
    have hexp : -((1/2 : ℝ)^3/(8*(beta/scale)^2))=-(r : ℝ)/(64*beta^2) := by
      simp only [div_pow]
      rw [hs2]
      field_simp [hrR.ne',hBeta0.ne']
      <;> ring
    rw [hexp] at hTail
    have hsub : Gᶜ ⊆ {v : Shao.Path r | Shao.energy v≤(r : ℝ)/2} := by
      intro v hv
      change ¬(r : ℝ)/2≤Shao.energy v at hv
      exact (lt_of_not_ge hv).le
    have hle : Pprefix.real Gᶜ≤Real.exp (-(r : ℝ)/(64*beta^2)) :=
      (measureReal_mono hsub).trans hTail
    have ha : 0<(r : ℝ)/(64*beta^2) := by positivity
    have heq : Real.exp (-(r : ℝ)/(64*beta^2))≤64*beta^2/(r : ℝ) := by
      have he : (r : ℝ)/(64*beta^2)≤Real.exp ((r : ℝ)/(64*beta^2)) :=
        (le_add_of_nonneg_right (by norm_num : (0:ℝ)≤1)).trans
          (Real.add_one_le_exp _)
      rw [show -(r : ℝ)/(64*beta^2)=-((r : ℝ)/(64*beta^2)) by ring,
        Real.exp_neg,←one_div]
      calc
        1/Real.exp ((r : ℝ)/(64*beta^2))≤1/((r : ℝ)/(64*beta^2)) :=
          one_div_le_one_div_of_le ha he
        _ = _ := by field_simp
    exact hle.trans heq
  let signs : Finset ℝ := SourceActualLocalProfileBudget.wallSigns I
  have hSign (eta : ℝ) (heta : eta∈signs) : eta=1 ∨ eta= -1 := by
    cases I with
    | upper => exact Or.inl (by simpa [signs,SourceActualLocalProfileBudget.wallSigns] using heta)
    | lower => exact Or.inr (by simpa [signs,SourceActualLocalProfileBudget.wallSigns] using heta)
    | interval => simpa [signs,SourceActualLocalProfileBudget.wallSigns] using heta
  have hAliveA (v : Shao.Path r)
      (hv : sourceAlive I (a v) x r (Equiv.refl (Fin n)))
      (eta : ℝ) (heta : eta∈signs) : v∈A eta := by
    intro k hk
    have hh := hv.2.2 k.val (by omega)
    change Interior I (actualWall (a v) x) (Shao.prefixSum (a v) k.val) at hh
    rw [(hAppend v).2.2.1 k.val (by omega)] at hh
    have he : actualWall (a v) x=wall v := by rw [actualWall,(hAppend v).1]
    rw [he] at hh
    cases I with
    | upper => have hη : eta=1 := by simpa [signs,SourceActualLocalProfileBudget.wallSigns] using heta
               change Shao.prefixSum v k.val<wall v at hh
               simpa only [hη,one_mul] using hh
    | lower => have hη : eta= -1 := by simpa [signs,SourceActualLocalProfileBudget.wallSigns] using heta
               change -wall v<Shao.prefixSum v k.val at hh
               simp only [hη,neg_one_mul]
               linarith
    | interval => rcases hSign eta heta with rfl | rfl
                  · simpa only [one_mul] using hh.2
                  · simp only [neg_one_mul]; linarith [hh.1]
  have hDom (v : Shao.Path r) : discrepancy v≤
      Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v+q 1 v+q (-1) v := by
    by_cases hg : v∈G
    · have hg' : v∉Gᶜ := by simpa using hg
      rw [Set.indicator_of_notMem hg',zero_add]
      have hd := (hCorr v).2.2.2.2
      change discrepancy v ≤ if 0<remainingEnergy (a v) r (Equiv.refl (Fin n)) ∧
          sourceAlive I (a v) x r (Equiv.refl (Fin n)) then
        ∑ eta∈signs, ((if 0<actualWall (a v) x-eta*Shao.prefixSum (a v) r ∧
            actualWall (a v) x-eta*Shao.prefixSum (a v) r≤
              2*((Finset.Icc 0 (n-r)).sup'
                (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩)
                (fun l => |Shao.prefixSum (a v) (r+l)-Shao.prefixSum (a v) r|))
            then 1 else 0)+
          (if 2*((Finset.Icc 0 (n-r)).sup'
              (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩)
              (fun l => |Shao.prefixSum (a v) (r+l)-Shao.prefixSum (a v) r|))<
                actualWall (a v) x-eta*Shao.prefixSum (a v) r
            then 2*Real.exp (-((actualWall (a v) x-eta*Shao.prefixSum (a v) r)^2)/
              (32*remainingEnergy (a v) r (Equiv.refl (Fin n)))) else 0)) else 0 at hd
      rw [hRemaining v,hSuffixMax v] at hd
      have he : actualWall (a v) x=wall v := by rw [actualWall,(hAppend v).1]
      rw [he,(hAppend v).2.2.1 r le_rfl] at hd
      by_cases hv : sourceAlive I (a v) x r (Equiv.refl (Fin n))
      · simp only [hU,hv,and_self,ite_true] at hd
        have hterm (eta : ℝ) (heta : eta∈signs) :
            ((if 0<gap eta v ∧ gap eta v≤2*J then 1 else 0)+
              (if 2*J<gap eta v then 2*Real.exp (-((gap eta v)^2)/(32*U)) else 0))
              ≤q eta v := by
          have ha := hAliveA v hv eta heta
          have hp := hgapPos eta v ha
          have hmem : v∈A eta∩G := ⟨ha,hg⟩
          simp only [q,Set.indicator_of_mem hmem]
          by_cases hnear : gap eta v≤2*J
          · have hfar : ¬2*J<gap eta v := not_lt.mpr hnear
            have hconj : 0<gap eta v ∧ gap eta v≤2*J := ⟨hp,hnear⟩
            simp only [if_pos hconj,if_neg hfar,if_pos hnear]
            linarith [Real.exp_pos (-((gap eta v)^2)/(32*U))]
          · have hfar : 2*J<gap eta v := lt_of_not_ge hnear
            have hnconj : ¬(0<gap eta v ∧ gap eta v≤2*J) := fun hh => hnear hh.2
            simp only [if_neg hnconj,if_pos hfar,if_neg hnear]
            linarith
        have hs : discrepancy v≤∑ eta∈signs,q eta v :=
          hd.trans (Finset.sum_le_sum fun eta heta => hterm eta heta)
        apply hs.trans
        cases I with
        | upper => simpa [signs,SourceActualLocalProfileBudget.wallSigns] using (show q 1 v≤q 1 v+q (-1) v from le_add_of_nonneg_right (hq0 (-1) v))
        | lower => simpa [signs,SourceActualLocalProfileBudget.wallSigns] using (show q (-1) v≤q 1 v+q (-1) v from le_add_of_nonneg_left (hq0 1 v))
        | interval => norm_num [signs,SourceActualLocalProfileBudget.wallSigns]
      · simp only [hv,and_false,ite_false] at hd
        exact hd.trans (add_nonneg (hq0 1 v) (hq0 (-1) v))
    · have hg' : v∈Gᶜ := hg
      rw [Set.indicator_of_mem hg']
      exact (hD1 v).trans (by linarith [hq0 1 v,hq0 (-1) v])
  have hLowi : Integrable (Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ))) Pprefix :=
    (integrable_const _).indicator hGM.compl
  have hLowone : (∫ v,Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v ∂Pprefix)=Pprefix.real Gᶜ := by
    change (∫ v,Gᶜ.indicator 1 v ∂Pprefix)=_
    exact integral_indicator_one hGM.compl
  have hInt := integral_mono hDi ((hLowi.add (hqi 1)).add (hqi (-1))) hDom
  simp only [Pi.add_apply] at hInt
  have hAdd1 :
      (∫ v,Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v+q 1 v+q (-1) v ∂Pprefix)=
        (∫ v,Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v+q 1 v ∂Pprefix)+
          (∫ v,q (-1) v ∂Pprefix) := by
    simpa only [Pi.add_apply] using integral_add (hLowi.add (hqi 1)) (hqi (-1))
  have hAdd2 :
      (∫ v,Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v+q 1 v ∂Pprefix)=
        (∫ v,Gᶜ.indicator (fun _ : Shao.Path r => (1:ℝ)) v ∂Pprefix)+
          (∫ v,q 1 v ∂Pprefix) := by
    simpa only [Pi.add_apply] using integral_add hLowi (hqi 1)
  rw [hAdd1,hAdd2,hLowone] at hInt
  have hp := hqb 1 (Or.inl rfl)
  have hm := hqb (-1) (Or.inr rfl)
  have htotal : (∫ v,discrepancy v ∂Pprefix)≤
      (16*CW*J^2+512*CW*U+(12*CW+64)*beta^2)/(r : ℝ) := by
    calc
      _ ≤64*beta^2/(r : ℝ)+CW*(8*J^2+256*U+6*beta^2)/(r : ℝ)+
          CW*(8*J^2+256*U+6*beta^2)/(r : ℝ) :=
        hInt.trans (add_le_add (add_le_add hLow hp) hm)
      _ = _ := by ring
  apply htotal.trans
  apply div_le_div_of_nonneg_right _ hrR.le
  nlinarith [mul_nonneg (sq_nonneg J) (show 0≤1008*CW+1024 by linarith),
    mul_nonneg hU0 (show 0≤512*CW+1024 by linarith),
    mul_nonneg (sq_nonneg beta) (show 0≤1012*CW+960 by linarith)]

theorem iid_actual_adaptive_terminal_budget :
    let K : ℝ := (2 : ℝ) ^ 64
    ∃ C : ℝ, 0 < C ∧
      ∀ {Ω : Type*} [MeasurableSpace Ω]
        (PB : Measure Ω) [IsProbabilityMeasure PB]
        (B : ℝ≥0 → Ω → ℝ), IsBrownianReal B PB →
        ∀ (rho : Measure ℝ) [IsProbabilityMeasure rho]
          (cap : ℝ), 0 < cap → (∀ᵐ z : ℝ ∂rho, |z| ≤ cap) →
          (∫ z : ℝ, z ∂rho) = 0 → (∫ z : ℝ, z ^ 2 ∂rho) = 1 →
          let beta : ℝ := ∫ z : ℝ, |z| ^ 3 ∂rho
          ∀ n : ℕ, 0 < n → ∀ x : ℝ, 16 ≤ x →
            cap ≤ Real.sqrt (n : ℝ) / (200 * x) →
            let delta : ℝ := beta / Real.sqrt (n : ℝ)
            let u : ℝ := delta * (1 + x) ^ 3
            u ≤ Real.exp (-3 * x ^ 2) →
            let h0 : ℝ := 4 * beta ^ 2
            let H : ℝ := K * beta ^ 2 * (1 + x) ^ 6
            let m : ℕ := ⌈H⌉₊
            let P : Measure (Shao.Path n) := Measure.pi (fun _ : Fin n => rho)
            let Q : Measure BridgeNoise := bridgeLaw B PB
            let tau : (Shao.Path n × LabelPerm n) → ℕ := fun p =>
              min (energyCutoff p.1 H p.2) (n - m)
            ∀ I : MonitoredDomain,
              let F : BridgeKernel := eventCompletionKernel I Q
              let terminal : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                if sourceAlive I p.1 x n p.2 then 1 else 0
              let discrepancy : (Shao.Path n × LabelPerm n) → ℝ := fun p =>
                (Finset.Icc (tau p) n).sup'
                  (by exact ⟨n, Finset.mem_Icc.mpr
                    ⟨(Nat.min_le_right _ _).trans (Nat.sub_le n m), le_rfl⟩⟩)
                  (fun j => |sourceValue I F p.1 x j p.2 - terminal p|)
              Measurable discrepancy ∧ Integrable discrepancy (revealLaw P) ∧
                (∫ p, discrepancy p ∂revealLaw P) ≤ C * H / (n : ℝ) ∧
                (∫ p, discrepancy p ∂revealLaw P) ≤
                  C * delta * Shao.standardNormalTail x := by
  classical
  intro K
  obtain ⟨CF,hCF,hFixed⟩ := aat_actual_fixed_suffix_terminal_budget
  let CT : ℝ := 12+240*CF
  let C : ℝ := CT*(1+(8/3 : ℝ)*K)
  have hK : 0<K := by dsimp [K]; positivity
  have hCT : 0<CT := by dsimp [CT]; positivity
  have hC : 0<C := by dsimp [C]; positivity
  refine ⟨C,hC,?_⟩
  intro Ω _ PB _ B hB rho hrho cap hcap0 hcapAE hmean hsecond beta n hn x hx hcap
    delta u hu h0 H m P Q tau I F terminal discrepancy
  letI : IsProbabilityMeasure rho := hrho
  letI : IsProbabilityMeasure Q := isProbabilityMeasure_bridgeLaw B PB hB
  have hnR : 0<(n : ℝ) := by exact_mod_cast hn
  have hnS : 0<Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnR
  have h2 : Integrable (fun z : ℝ => z^2) rho := by
    apply Integrable.of_bound (by fun_prop) (cap^2)
    filter_upwards [hcapAE] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg z),←sq_abs z]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 2
  have h3 : Integrable (fun z : ℝ => |z|^3) rho := by
    apply Integrable.of_bound (by fun_prop) (cap^3)
    filter_upwards [hcapAE] with z hz
    rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg (abs_nonneg z) 3)]
    exact pow_le_pow_left₀ (abs_nonneg z) hz 3
  have hBeta : 1≤beta :=
    Shao.C2.AuxiliaryEnergyCentered.auxiliary_absolute_third_moment_ge_one rho h2 h3 hsecond
  have hBeta0 : 0<beta := by linarith
  have hx0 : 0<x := by linarith
  have hx1 : 1≤x := by linarith
  have hdelta : 0<delta := by dsimp [delta]; positivity
  have hu0 : 0<u := by dsimp [u]; positivity
  have hH : 0<H := by dsimp [H]; positivity
  have hh0 : 0<h0 := by dsimp [h0]; positivity
  have hexp1 : 2≤Real.exp 1 := by
    have hh := Real.add_one_le_exp (1:ℝ)
    norm_num at hh
    exact hh
  have hHratio : H/(n : ℝ)=K*u^2 := by
    dsimp only [H,u,delta]
    rw [mul_pow,div_pow,Real.sq_sqrt hnR.le]
    ring
  have hHsmall : H/(n : ℝ)≤1/8 := by
    have hu2 : u^2≤Real.exp (-6*x^2) := by
      have hh := pow_le_pow_left₀ hu0.le hu 2
      have he : (Real.exp (-3*x^2))^2=Real.exp (-6*x^2) := by
        rw [←Real.exp_nat_mul]
        congr 1
        ring
      exact hh.trans_eq he
    have h67 : (67:ℝ)≤6*x^2 := by nlinarith [sq_nonneg (x-16)]
    have he67 : (2:ℝ)^67≤Real.exp 67 := by
      have he := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤2) hexp1 67
      convert he using 1
      rw [←Real.exp_nat_mul]
      norm_num
    have he : Real.exp (-6*x^2)≤1/(2:ℝ)^67 := by
      have hh : (2:ℝ)^67≤Real.exp (6*x^2) :=
        he67.trans (Real.exp_le_exp.2 h67)
      rw [show -6*x^2=-(6*x^2) by ring,Real.exp_neg,←one_div]
      exact one_div_le_one_div_of_le (by positivity) hh
    rw [hHratio]
    calc
      K*u^2≤K*(1/(2:ℝ)^67) := mul_le_mul_of_nonneg_left (hu2.trans he) hK.le
      _ = 1/8 := by norm_num [K]
  have hHle : H≤(n : ℝ)/8 := by
    have hh := (div_le_iff₀ hnR).1 hHsmall
    linarith
  have hp6 : 1≤(1+x)^6 := one_le_pow₀ (by linarith : (1:ℝ)≤1+x)
  have hK4 : (4:ℝ)≤K := by norm_num [K]
  have hH4 : (4:ℝ)≤H := by
    have hb2 : (1:ℝ)≤beta^2 := one_le_pow₀ hBeta
    have hh := mul_le_mul hb2 hp6 (by norm_num) (sq_nonneg beta)
    dsimp only [H]
    nlinarith [mul_le_mul_of_nonneg_left hh hK.le]
  have hn32 : 32≤n := by
    have hh : (32:ℝ)≤(n : ℝ) := by linarith
    exact_mod_cast hh
  have hn4 : 4≤n := by omega
  have hmR : (m : ℝ)≤H+1 := by
    exact (Nat.ceil_lt_add_one hH.le).le
  have hm3 : (m : ℝ)≤3*H := by linarith
  have hmL : m≤n/2 := by
    have hm2 : 2*m≤n := by
      have hh : (2:ℝ)*(m : ℝ)≤(n : ℝ) := by linarith
      exact_mod_cast hh
    omega
  have hm1 : 1≤m := by
    have hh : H≤(m : ℝ) := Nat.le_ceil H
    by_contra hm
    have hmz : m=0 := by omega
    simp only [hmz,Nat.cast_zero] at hh
    linarith
  have hhH : h0≤H := by
    have hp : 4≤K*(1+x)^6 := by
      have hh := mul_le_mul_of_nonneg_left hp6 hK.le
      linarith
    dsimp only [h0,H]
    nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg beta)]
  let normalizedLaw : Measure ℝ := Measure.map (fun z : ℝ => z/Real.sqrt (n : ℝ)) rho
  let R0 : ℝ := Shao.truncationBudget normalizedLaw n 0
  let h : ℝ := 4*(n : ℝ)*R0^2
  have hR0 : 0≤R0 := by
    dsimp [R0,Shao.truncationBudget]
    exact mul_nonneg (Nat.cast_nonneg _) (integral_nonneg fun z => Shao.truncationF_nonneg _)
  have hRle : R0≤delta := by
    have hFi : Integrable (fun z : ℝ => Shao.truncationF (z/Real.sqrt (n : ℝ))) rho := by
      simpa only [div_eq_mul_inv,one_div,mul_comm] using
        Shao.integrable_truncationF_mul rho h2 ((Real.sqrt (n : ℝ))⁻¹)
    have hCi : Integrable (fun z : ℝ => |z/Real.sqrt (n : ℝ)|^3) rho := by
      simpa only [abs_div,abs_of_pos hnS,div_pow] using h3.div_const (Real.sqrt (n : ℝ)^3)
    have hpoint (z : ℝ) : Shao.truncationF (z/Real.sqrt (n : ℝ))≤
        |z/Real.sqrt (n : ℝ)|^3 := by
      unfold Shao.truncationF
      calc
        _ ≤ (z/Real.sqrt (n : ℝ))^2*|z/Real.sqrt (n : ℝ)| :=
          mul_le_mul_of_nonneg_left (min_le_left _ _) (sq_nonneg _)
        _ = _ := by rw [←sq_abs (z/Real.sqrt (n : ℝ))]; ring
    calc
      R0=(n : ℝ)*(∫ z : ℝ,Shao.truncationF (z/Real.sqrt (n : ℝ)) ∂rho) := by
        dsimp [R0,normalizedLaw,Shao.truncationBudget]
        simp only [add_zero,one_mul]
        rw [integral_map (μ := rho) (φ := fun z : ℝ => z/Real.sqrt (n : ℝ))
          (measurable_id.div_const _).aemeasurable Shao.continuous_truncationF.aestronglyMeasurable]
      _ ≤ (n : ℝ)*(∫ z : ℝ,|z/Real.sqrt (n : ℝ)|^3 ∂rho) :=
        mul_le_mul_of_nonneg_left (integral_mono hFi hCi hpoint) hnR.le
      _ = delta := by
        simp only [abs_div,abs_of_pos hnS,div_pow]
        rw [integral_div]
        change (n : ℝ)*(beta/Real.sqrt (n : ℝ)^3)=beta/Real.sqrt (n : ℝ)
        field_simp
        nlinarith [Real.sq_sqrt hnR.le]
  have hdeltaU : delta≤u := by
    have hp : 1≤(1+x)^3 := one_le_pow₀ (by linarith : (1:ℝ)≤1+x)
    dsimp only [u]
    nlinarith [mul_le_mul_of_nonneg_left hp hdelta.le]
  have hRhalf : R0≤1/2 := by
    have he : Real.exp (-3*x^2)≤1/2 := by
      have hh : 2≤Real.exp (3*x^2) :=
        hexp1.trans (Real.exp_le_exp.2 (by nlinarith [sq_nonneg (x-16)]))
      rw [show -3*x^2=-(3*x^2) by ring,Real.exp_neg,←one_div]
      exact one_div_le_one_div_of_le (by norm_num) hh
    exact hRle.trans (hdeltaU.trans (hu.trans he))
  have hhH' : h≤H := by
    have hsq : R0^2≤delta^2 := pow_le_pow_left₀ hR0 hRle 2
    have hdel : (n : ℝ)*delta^2=beta^2 := by
      dsimp [delta]
      rw [div_pow,Real.sq_sqrt hnR.le]
      field_simp
    have hh : h≤h0 := by
      dsimp only [h,h0]
      nlinarith [mul_le_mul_of_nonneg_left hsq hnR.le]
    exact hh.trans hhH
  let L : ℕ := n/2
  let rev : Shao.Path n → Shao.Path n := fun a i => a (Fin.rev i)
  let Qrev : Shao.Path n → ℕ → ℝ := fun a k => Shao.prefixSquares (rev a) k
  let NH : Shao.Path n → ℕ := fun a =>
    @dite ℕ (∃ k : ℕ,k≤L ∧ H≤Qrev a k) (Classical.propDecidable _)
      (fun he => @Nat.find (fun k : ℕ => k≤L ∧ H≤Qrev a k)
        (fun k => Classical.propDecidable _) he) (fun _ => L)
  let N : Shao.Path n → ℕ := fun a => max m (NH a)
  let rank : Shao.Path n → ℕ := fun a => n-N a
  let suffixEnergy : Shao.Path n → ℝ := fun a => Shao.energy a-Shao.prefixSquares a (rank a)
  let suffixMax : Shao.Path n → ℝ := fun a =>
    (Finset.Icc 0 (N a)).sup'
      (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩)
      (fun l => |Shao.prefixSum a (rank a+l)-Shao.prefixSum a (rank a)|)
  let exceptional : Set (Shao.Path n) := {a | Qrev a L<H}
  let tau0 : Shao.Path n → ℕ := fun a => min (energyCutoff a H (Equiv.refl (Fin n))) (n-m)
  have hRaw := actual_backward_terminal_raw_data rho n hn4 h2 hmean (by rw [hsecond]; norm_num)
  specialize hRaw (by convert hRhalf using 1 <;> simp only [hsecond,mul_one] <;> rfl) H
    (by convert hhH' using 1 <;> simp only [hsecond,mul_one] <;> rfl) m hmL
    (by simpa only [hsecond,div_one] using hm3)
  obtain ⟨_,_,_,hNHM,hNM,hUM,hJM,htauM,hRanks,hNHi,hNi,hUi,hJ2i,
    hNHb,hNb,hExb,hUeq,hJb⟩ := hRaw
  change Measurable NH at hNHM
  change Measurable N at hNM
  change Measurable suffixEnergy at hUM
  change Measurable suffixMax at hJM
  change Measurable tau0 at htauM
  change (∀ a,1≤NH a ∧ NH a≤N a ∧ N a≤L ∧ suffixEnergy a=Qrev a (N a) ∧
    (a∉exceptional → tau0 a=if NH a≤m then rank a else rank a+1)) at hRanks
  change Integrable (fun a => (NH a : ℝ)) P at hNHi
  change Integrable (fun a => (N a : ℝ)) P at hNi
  change Integrable suffixEnergy P at hUi
  change Integrable (fun a => suffixMax a^2) P at hJ2i
  change (∫ a,(NH a : ℝ) ∂P)≤4*H/(∫ z : ℝ,z^2 ∂rho) at hNHb
  change (∫ a,(N a : ℝ) ∂P)≤7*H/(∫ z : ℝ,z^2 ∂rho) at hNb
  change P.real exceptional≤12*H/((n : ℝ)*(∫ z : ℝ,z^2 ∂rho)) at hExb
  change (∫ a,suffixEnergy a ∂P)=(∫ z : ℝ,z^2 ∂rho)*(∫ a,(N a : ℝ) ∂P) at hUeq
  change (∫ a,suffixMax a^2 ∂P)≤16*(∫ z : ℝ,z^2 ∂rho)*(∫ a,(N a : ℝ) ∂P) at hJb
  rw [hsecond,div_one] at hNHb hNb
  rw [hsecond,mul_one] at hExb
  rw [hsecond,one_mul] at hUeq
  rw [hsecond,mul_one] at hJb
  have hUb : (∫ a,suffixEnergy a ∂P)≤7*H := by rw [hUeq]; simpa using hNb
  have hJb' : (∫ a,suffixMax a^2 ∂P)≤112*H := by nlinarith
  have hUM0 (a : Shao.Path n) : 0≤suffixEnergy a :=
    (remaining_population_geometry a (rank a) (Nat.sub_le n _) (Equiv.refl (Fin n))).1
  have hJM0 (a : Shao.Path n) : 0≤suffixMax a :=
    (abs_nonneg _).trans (Finset.le_sup'
      (fun l => |Shao.prefixSum a (rank a+l)-Shao.prefixSum a (rank a)|)
      (Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩))
  let terminal0 : Shao.Path n → ℝ := fun a =>
    if sourceAlive I a x n (Equiv.refl (Fin n)) then 1 else 0
  let d : Shao.Path n → ℕ → ℝ := fun a j =>
    |sourceValue I F a x j (Equiv.refl (Fin n))-terminal0 a|
  let D : (k : Shao.Path n → ℕ) → (∀ a,k a≤n) → Shao.Path n → ℝ :=
    fun k hk a => (Finset.Icc (k a) n).sup'
      (by exact ⟨n,Finset.mem_Icc.2 ⟨hk a,le_rfl⟩⟩) (d a)
  have hF : Measurable F := by
    cases I with
    | upper => exact Shao.C2.CompletionMeasurability.measurable_upperCompletion_parameters Q
    | lower => exact Shao.C2.CompletionMeasurability.measurable_lowerCompletion_parameters Q
    | interval => exact Shao.C2.CompletionMeasurability.measurable_intervalCompletion_parameters Q
  have hwallM : Measurable (fun a : Shao.Path n => actualWall a x) := Shao.measurable_energyWall x
  have hInteriorM (f : Shao.Path n → ℝ) (hf : Measurable f) :
      MeasurableSet {a | Interior I (actualWall a x) (f a)} := by
    cases I with
    | upper => exact measurableSet_lt hf hwallM
    | lower => exact measurableSet_lt hwallM.neg hf
    | interval => exact (measurableSet_lt hwallM.neg hf).inter (measurableSet_lt hf hwallM)
  have hAliveM (j : ℕ) :
      MeasurableSet {a : Shao.Path n | sourceAlive I a x j (Equiv.refl (Fin n))} := by
    have hp : MeasurableSet {a : Shao.Path n | ∀ k : ℕ,k≤j →
        Interior I (actualWall a x) (Shao.prefixSum a k)} := by
      rw [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro k
      by_cases hk : k≤j
      · simpa only [hk,true_implies] using hInteriorM _ (Shao.measurable_prefixSum k)
      · simp only [hk,false_implies,Set.setOf_true,MeasurableSet.univ]
    exact (measurableSet_lt measurable_const Shao.measurable_energy).inter
      ((hInteriorM _ (Shao.measurable_prefixSum n)).inter hp)
  have hterminalM : Measurable terminal0 :=
    Measurable.ite (hAliveM n) measurable_const measurable_const
  have hSourceM (j : ℕ) : Measurable
      (fun a : Shao.Path n => sourceValue I F a x j (Equiv.refl (Fin n))) := by
    have hy := Shao.measurable_prefixSum (n := n) j
    have hz := Shao.measurable_prefixSum (n := n) n
    have hT : Measurable (fun a : Shao.Path n => remainingEnergy a j (Equiv.refl (Fin n))) :=
      Shao.measurable_energy.sub (Shao.measurable_prefixSquares j)
    have hGuard : MeasurableSet {a : Shao.Path n | 0<actualWall a x ∧
        Interior I (actualWall a x) (Shao.prefixSum a j) ∧
        Interior I (actualWall a x) (Shao.prefixSum a n)} :=
      (measurableSet_lt measurable_const hwallM).inter
        ((hInteriorM _ hy).inter (hInteriorM _ hz))
    unfold sourceValue completionExt
    exact Measurable.ite (hAliveM j)
      (Measurable.ite hGuard
        (Measurable.ite (measurableSet_lt measurable_const hT)
          (hF.comp (hwallM.prodMk (hy.prodMk (hT.prodMk hz))))
          (Measurable.ite
            ((measurableSet_eq_fun hT measurable_const).inter (measurableSet_eq_fun hy hz))
            measurable_const measurable_const)) measurable_const) measurable_const
  have hdM (j : ℕ) : Measurable (fun a : Shao.Path n => d a j) :=
    continuous_abs.measurable.comp ((hSourceM j).sub hterminalM)
  have hD0 (k : Shao.Path n → ℕ) (hk : ∀ a,k a≤n) (a : Shao.Path n) : 0≤D k hk a :=
    (abs_nonneg _).trans (Finset.le_sup' (d a) (Finset.mem_Icc.2 ⟨hk a,le_rfl⟩))
  have hD1 (k : Shao.Path n → ℕ) (hk : ∀ a,k a≤n) (a : Shao.Path n) : D k hk a≤1 :=
    (actual_source_terminal_corridor_envelope PB B hB n a (k a) (hk a) x hx0.le I).2.1
  have hDM (k : Shao.Path n → ℕ) (hk : ∀ a,k a≤n) (hkm : Measurable k) :
      Measurable (D k hk) := by
    let f : ℕ → Shao.Path n → ℝ := fun j a => if k a≤j then d a j else 0
    have hfm (j : ℕ) (hj : j∈Finset.Icc 0 n) : Measurable (f j) :=
      Measurable.ite (measurableSet_le hkm measurable_const) (hdM j) measurable_const
    have heq (a : Shao.Path n) :
        D k hk a=(Finset.Icc 0 n).sup'
          (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩) (fun j => f j a) := by
      apply le_antisymm
      · apply Finset.sup'_le
        intro j hj
        have hjn := (Finset.mem_Icc.1 hj).2
        have hkj := (Finset.mem_Icc.1 hj).1
        have hh := Finset.le_sup' (fun j => f j a)
          (Finset.mem_Icc.2 ⟨Nat.zero_le j,hjn⟩)
        simpa only [f,if_pos hkj] using hh
      · apply Finset.sup'_le
        intro j hj
        by_cases hkj : k a≤j
        · simpa only [f,if_pos hkj] using
            Finset.le_sup' (d a) (Finset.mem_Icc.2 ⟨hkj,(Finset.mem_Icc.1 hj).2⟩)
        · simpa only [f,if_neg hkj] using hD0 k hk a
    have hfSup := Finset.measurable_sup' (s := Finset.Icc 0 n)
      (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩) hfm
    convert hfSup using 1
    ext a
    rw [heq a]
    exact (Finset.sup'_apply
      (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩) f a).symm
  have hDi (k : Shao.Path n → ℕ) (hk : ∀ a,k a≤n) (hkm : Measurable k) :
      Integrable (D k hk) P := by
    apply Integrable.of_bound (hDM k hk hkm).aestronglyMeasurable 1
    exact ae_of_all _ fun a => by
      rw [Real.norm_eq_abs,abs_of_nonneg (hD0 k hk a)]
      exact hD1 k hk a
  have htauN (a : Shao.Path n) : tau0 a≤n :=
    (Nat.min_le_right _ _).trans (Nat.sub_le n m)
  have hrankN (a : Shao.Path n) : rank a≤n := Nat.sub_le n _
  have hrankM : Measurable rank := measurable_const.sub hNM
  let adaptive : Shao.Path n → ℝ := D tau0 htauN
  let fromRank : Shao.Path n → ℝ := D rank hrankN
  let payment : Shao.Path n → ℝ := fun a =>
    (2*CF/(n : ℝ))*(suffixMax a^2+suffixEnergy a+H)
  have hpaymentM : Measurable payment :=
    measurable_const.mul (((hJM.pow_const 2).add hUM).add_const H)
  have hpaymenti : Integrable payment P := by
    simpa only [payment,Pi.add_apply] using
      (((hJ2i.add hUi).add (integrable_const H)).const_mul (2*CF/(n : ℝ)))
  have hpayment0 (a : Shao.Path n) : 0≤payment a := by
    dsimp only [payment]
    exact mul_nonneg (by positivity)
      (add_nonneg (add_nonneg (sq_nonneg _) (hUM0 a)) hH.le)
  have hExceptionalM : MeasurableSet exceptional := by
    have hrev : Measurable rev := Measurable.of_eval fun i => measurable_pi_apply (Fin.rev i)
    exact measurableSet_lt ((Shao.measurable_prefixSquares L).comp hrev) measurable_const
  have hPathDom (a : Shao.Path n) : adaptive a≤
      exceptional.indicator (fun _ : Shao.Path n => (1:ℝ)) a+fromRank a := by
    by_cases ha : a∈exceptional
    · rw [Set.indicator_of_mem ha]
      exact (hD1 tau0 htauN a).trans (by linarith [hD0 rank hrankN a])
    · rw [Set.indicator_of_notMem ha,zero_add]
      have hrt : rank a≤tau0 a := by
        rw [(hRanks a).2.2.2.2 ha]
        split_ifs <;> omega
      apply Finset.sup'_le
      intro j hj
      exact Finset.le_sup' (d a)
        (Finset.mem_Icc.2 ⟨hrt.trans (Finset.mem_Icc.1 hj).1,(Finset.mem_Icc.1 hj).2⟩)
  have hMerge (nn rr tt : ℕ) (hlen : nn=rr+tt) :
      let merge : Shao.Path rr×Shao.Path tt → Shao.Path nn := fun p i =>
        Fin.append p.1 p.2 (finCongr hlen i)
      let «prefix» : Shao.Path nn → Shao.Path rr := fun a i => a ⟨i.val,by have := i.is_lt; omega⟩
      let suffix : Shao.Path nn → Shao.Path tt := fun a i => a ⟨rr+i.val,by have := i.is_lt; omega⟩
      Measurable merge ∧ (∀ a,merge («prefix» a,suffix a)=a) ∧
      ∀ p,Shao.energy (merge p)=Shao.energy p.1+Shao.energy p.2 ∧
        Shao.prefixSquares (merge p) rr=Shao.energy p.1 ∧
        ∀ l,Shao.prefixSum (merge p) (rr+l)-Shao.prefixSum (merge p) rr=Shao.prefixSum p.2 l := by
    subst nn
    intro merge «prefix» suffix
    have hm : Measurable merge := by
      apply Measurable.of_eval
      intro i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simpa only [merge,finCongr_refl,Equiv.refl_apply,Fin.append_left,Function.comp_def] using
          (measurable_pi_apply j : Measurable (fun v : Shao.Path rr => v j)).comp measurable_fst
      · intro j
        simpa only [merge,finCongr_refl,Equiv.refl_apply,Fin.append_right,Function.comp_def] using
          (measurable_pi_apply j : Measurable (fun b : Shao.Path tt => b j)).comp measurable_snd
    refine ⟨hm,?_,?_⟩
    · intro a
      ext i
      refine Fin.addCases ?_ ?_ i
      · intro j
        simp only [merge,finCongr_refl,Equiv.refl_apply,Fin.append_left,«prefix»]
        rfl
      · intro j
        simp only [merge,finCongr_refl,Equiv.refl_apply,Fin.append_right,suffix]
        rfl
    · intro p
      have he : Shao.energy (merge p)=Shao.energy p.1+Shao.energy p.2 := by
        simp only [merge,finCongr_refl,Equiv.refl_apply]
        unfold Shao.energy
        rw [Fin.sum_univ_add]
        simp only [Fin.append_left,Fin.append_right]
      have hq : Shao.prefixSquares (merge p) rr=Shao.energy p.1 := by
        rw [Shao.prefixSquares,Finset.sum_filter,Fin.sum_univ_add]
        have hl (i : Fin rr) : i.val<rr := i.is_lt
        have ht (i : Fin tt) : ¬rr+i.val<rr := by omega
        simp [merge,hl,ht,Shao.energy]
      have hh : Spitzer.head (merge p) rr (Nat.le_add_right rr tt)=p.1 := by
        ext i
        exact Fin.append_left _ _ _
      have hp : Shao.prefixSum (merge p) rr=Shao.prefixSum p.1 rr :=
        (by have h := Spitzer.head_prefixSum (merge p) rr (Nat.le_add_right rr tt) rr le_rfl
            rw [hh] at h
            exact h.symm)
      refine ⟨he,hq,?_⟩
      intro l
      have hpa : Shao.prefixSum (merge p) (rr+l)=
          Shao.prefixSum p.1 rr+Shao.prefixSum p.2 l := by
        simpa only [merge,finCongr_refl,Equiv.refl_apply] using
          Shao.OQ4.prefixSum_append rr tt p.1 p.2 l
      rw [hpa,hp]
      ring
  have hFixedAt (nn rr tt : ℕ) (hlen : nn=rr+tt)
      (hrr : 0<rr) (httr : tt≤rr)
      (hcap' : cap≤Real.sqrt (nn : ℝ)/(200*x)) (b : Shao.Path tt) :
      let joined : Shao.Path rr → Shao.Path nn := fun v i =>
        Fin.append v b (finCongr hlen i)
      let final : Shao.Path rr → ℝ := fun v =>
        if sourceAlive I (joined v) x nn (Equiv.refl (Fin nn)) then 1 else 0
      let bill : Shao.Path rr → ℝ := fun v =>
        (Finset.Icc rr nn).sup'
          (by exact ⟨rr,Finset.mem_Icc.2 ⟨le_rfl,by omega⟩⟩)
          (fun j => |sourceValue I F (joined v) x j (Equiv.refl (Fin nn))-final v|)
      let suffixJ : ℝ := (Finset.Icc 0 tt).sup'
        (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩)
        (fun l => |Shao.prefixSum b l|)
      (∫ v,bill v ∂Measure.pi (fun _ : Fin rr => rho))≤
        CF*(suffixJ^2+Shao.energy b+beta^2)/(rr : ℝ) := by
    subst nn
    simpa only [finCongr_refl,Equiv.refl_apply] using
      (hFixed PB B hB rho cap hcap0 hcapAE hmean hsecond rr tt hrr httr x hx1 hcap' I b).2.2
  have hSelected (t : ℕ) (htmem : t∈Finset.Icc 1 L) :
      (∫ a,if N a=t then fromRank a else 0 ∂P)≤
        ∫ a,if N a=t then payment a else 0 ∂P := by
    have htL : t≤L := (Finset.mem_Icc.1 htmem).2
    have htn : t≤n := htL.trans (Nat.div_le_self n 2)
    have hrt : t≤n-t := by dsimp [L] at htL; omega
    have hrp : 0<n-t := by dsimp [L] at htL; omega
    have hrn : n-t≤n := Nat.sub_le n t
    let «prefix» : Shao.Path n → Shao.Path (n-t) := fun a i =>
      a ⟨i.val,lt_of_lt_of_le i.is_lt (Nat.sub_le n t)⟩
    let suffix : Shao.Path n → Shao.Path t := fun a i =>
      a ⟨n-t+i.val,by have := i.is_lt; omega⟩
    let merge : Shao.Path (n-t)×Shao.Path t → Shao.Path n := fun p i =>
      Fin.append p.1 p.2 (finCongr (by omega : n=(n-t)+t) i)
    let Ppre : Measure (Shao.Path (n-t)) := Measure.pi (fun _ : Fin (n-t) => rho)
    let Psuf : Measure (Shao.Path t) := Measure.pi (fun _ : Fin t => rho)
    let Phi : Shao.Path (n-t)×Shao.Path t → ℝ :=
      fun p => D (fun _ => n-t) (fun _ => hrn) (merge p)
    let previousEnergy : Shao.Path t → ℝ := fun b =>
      Shao.prefixSquares (fun i : Fin t => b (Fin.rev i)) (t-1)
    let selectedSuffix : Set (Shao.Path t) := {b |
      if t<m then False
      else if t=m then (if t=L then True else H≤Shao.energy b)
      else if t<L then previousEnergy b<H ∧ H≤Shao.energy b
      else previousEnergy b<H}
    let suffixJ : Shao.Path t → ℝ := fun b =>
      (Finset.Icc 0 t).sup'
        (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩)
        (fun l => |Shao.prefixSum b l|)
    let cost : Shao.Path t → ℝ := fun b =>
      (2*CF/(n : ℝ))*(suffixJ b^2+Shao.energy b+H)
    have hmrg := hMerge n (n-t) t (by omega)
    change Measurable merge ∧ (∀ a,merge («prefix» a,suffix a)=a) ∧
      (∀ p,Shao.energy (merge p)=Shao.energy p.1+Shao.energy p.2 ∧
        Shao.prefixSquares (merge p) (n-t)=Shao.energy p.1 ∧
        ∀ l,Shao.prefixSum (merge p) (n-t+l)-Shao.prefixSum (merge p) (n-t)=
          Shao.prefixSum p.2 l) at hmrg
    have hPhiM : Measurable Phi :=
      (hDM (fun _ => n-t) (fun _ => hrn) measurable_const).comp hmrg.1
    have hPhi1 (p : Shao.Path (n-t)×Shao.Path t) : |Phi p|≤1 := by
      rw [abs_of_nonneg (hD0 (fun _ => n-t) (fun _ => hrn) (merge p))]
      exact hD1 (fun _ => n-t) (fun _ => hrn) (merge p)
    have hFubini := actual_backward_stopped_suffix_integral rho n hn4 H hH m hmL
      t htL Phi hPhiM hPhi1
    change (∀ a,N a=t ↔ suffix a∈selectedSuffix) ∧
      Integrable (fun a => if N a=t then Phi («prefix» a,suffix a) else 0) P ∧
      Integrable (fun b => if b∈selectedSuffix then ∫ v,Phi (v,b) ∂Ppre else 0) Psuf ∧
      (∫ a,if N a=t then Phi («prefix» a,suffix a) else 0 ∂P)=
        ∫ b,if b∈selectedSuffix then ∫ v,Phi (v,b) ∂Ppre else 0 ∂Psuf at hFubini
    have hPhiComp (a : Shao.Path n) (ha : N a=t) : Phi («prefix» a,suffix a)=fromRank a := by
      simp only [Phi,fromRank,D,hmrg.2.1 a,rank,ha]
    have hJM' : Measurable suffixJ := by
      have hf (l : ℕ) (hl : l∈Finset.Icc 0 t) :
          Measurable (fun b : Shao.Path t => |Shao.prefixSum b l|) :=
        continuous_abs.measurable.comp (Shao.measurable_prefixSum l)
      convert Finset.measurable_sup' (s := Finset.Icc 0 t)
        (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩) hf using 1
      ext b
      exact (Finset.sup'_apply
        (by exact ⟨0,Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩⟩)
        (fun (l : ℕ) (b : Shao.Path t) => |Shao.prefixSum b l|) b).symm
    have hcostM : Measurable cost :=
      measurable_const.mul (((hJM'.pow_const 2).add Shao.measurable_energy).add_const H)
    have hpreviousM : Measurable previousEnergy :=
      (Shao.measurable_prefixSquares (t-1)).comp
        (Measurable.of_eval fun i => measurable_pi_apply (Fin.rev i))
    have hSelM : MeasurableSet selectedSuffix := by
      by_cases htm : t<m
      · simp only [selectedSuffix,if_pos htm,Set.setOf_false,MeasurableSet.empty]
      · by_cases he : t=m
        · by_cases htLast : t=L
          · simp only [selectedSuffix,if_neg htm,if_pos he,if_pos htLast,
              Set.setOf_true,MeasurableSet.univ]
          · simpa only [selectedSuffix,if_neg htm,if_pos he,if_neg htLast] using
              (measurableSet_le (measurable_const : Measurable (fun _ : Shao.Path t => H))
                Shao.measurable_energy)
        · by_cases htStrict : t<L
          · simp only [selectedSuffix,if_neg htm,if_neg he,if_pos htStrict]
            exact (measurableSet_lt hpreviousM measurable_const).inter
              (measurableSet_le measurable_const Shao.measurable_energy)
          · simpa only [selectedSuffix,if_neg htm,if_neg he,if_neg htStrict] using
              measurableSet_lt hpreviousM measurable_const
    have hcostComp (a : Shao.Path n) (ha : N a=t) : cost (suffix a)=payment a := by
      have hrank : rank a=n-t := by simp only [rank,ha]
      have hd := hmrg.2.2 («prefix» a,suffix a)
      rw [hmrg.2.1 a] at hd
      have hu : Shao.energy (suffix a)=suffixEnergy a := by
        dsimp only [suffixEnergy]
        rw [hrank,hd.1,hd.2.1]
        ring
      have hj : suffixJ (suffix a)=suffixMax a := by
        dsimp only [suffixJ,suffixMax]
        simp only [ha,hrank]
        congr 1
        ext l
        rw [hd.2.2 l]
      simp only [cost,payment,hu,hj]
    have hSection (b : Shao.Path t) :
        (∫ v,Phi (v,b) ∂Ppre)≤cost b := by
      have hh' := hFixedAt n (n-t) t (by omega) hrp hrt hcap b
      change (∫ v,Phi (v,b) ∂Ppre)≤
        CF*(suffixJ b^2+Shao.energy b+beta^2)/((n-t : ℕ) : ℝ) at hh'
      have hrR : 0<((n-t : ℕ) : ℝ) := by exact_mod_cast hrp
      have hhalf : (n : ℝ)/2≤((n-t : ℕ) : ℝ) := by
        have ht2 : 2*t≤n := by dsimp [L] at htL; omega
        have hrt' : (n : ℝ)=((n-t : ℕ) : ℝ)+(t : ℝ) := by exact_mod_cast (Nat.sub_add_cancel htn).symm
        have ht2' : 2*(t : ℝ)≤(n : ℝ) := by exact_mod_cast ht2
        linarith
      have hbH : beta^2≤H := by
        have hh : beta^2≤h0 := by dsimp [h0]; nlinarith [sq_nonneg beta]
        exact hh.trans hhH
      have hJpos : 0≤suffixJ b :=
        (abs_nonneg _).trans (Finset.le_sup' (fun l => |Shao.prefixSum b l|)
          (Finset.mem_Icc.2 ⟨le_rfl,Nat.zero_le _⟩))
      have hnum : 0≤CF*(suffixJ b^2+Shao.energy b+H) :=
        mul_nonneg hCF.le (add_nonneg (add_nonneg (sq_nonneg _) (Shao.energy_nonneg b)) hH.le)
      calc
        _ ≤CF*(suffixJ b^2+Shao.energy b+beta^2)/((n-t : ℕ) : ℝ) := hh'
        _ ≤CF*(suffixJ b^2+Shao.energy b+H)/((n-t : ℕ) : ℝ) := by
          apply div_le_div_of_nonneg_right _ hrR.le
          exact mul_le_mul_of_nonneg_left (by linarith) hCF.le
        _ ≤(2*CF/(n : ℝ))*(suffixJ b^2+Shao.energy b+H) := by
          have hfac : 1/((n-t : ℕ) : ℝ)≤2/(n : ℝ) :=
            (div_le_div_iff₀ hrR hnR).2 (by linarith)
          calc
            CF*(suffixJ b^2+Shao.energy b+H)/((n-t : ℕ) : ℝ)=
                (1/((n-t : ℕ) : ℝ))*(CF*(suffixJ b^2+Shao.energy b+H)) := by ring
            _ ≤(2/(n : ℝ))*(CF*(suffixJ b^2+Shao.energy b+H)) :=
              mul_le_mul_of_nonneg_right hfac hnum
            _ =_ := by ring
    let Gcost : Shao.Path (n-t)×Shao.Path t → ℝ :=
      fun p => if p.2∈selectedSuffix then cost p.2 else 0
    have hGcostM : Measurable Gcost :=
      Measurable.ite (hSelM.preimage measurable_snd) (hcostM.comp measurable_snd) measurable_const
    let split : Shao.Path n → Shao.Path (n-t)×Shao.Path t := fun a => («prefix» a,suffix a)
    have hsplit : MeasurePreserving split P (Ppre.prod Psuf) := by
      let e : Fin (n-t)⊕Fin t≃Fin n := finSumFinEquiv.trans (finCongr (Nat.sub_add_cancel htn))
      have h1 := (measurePreserving_piCongrLeft (fun _ : Fin n => rho) e).symm
      have h2' := measurePreserving_sumPiEquivProdPi (fun _ : Fin (n-t)⊕Fin t => rho)
      convert h2'.comp h1 using 1
      ext a i <;> rfl
    have hGcomp (a : Shao.Path n) : Gcost (split a)=if N a=t then payment a else 0 := by
      by_cases ha : N a=t
      · simp only [Gcost,split,if_pos ((hFubini.1 a).1 ha),if_pos ha,hcostComp a ha]
      · simp only [Gcost,split,if_neg (mt (hFubini.1 a).2 ha),if_neg ha]
    have hPaySel : Integrable (fun a => if N a=t then payment a else 0) P := by
      have hi := hpaymenti.indicator (measurableSet_eq_fun hNM
        (measurable_const : Measurable (fun _ : Shao.Path n => t)))
      apply hi.congr
      exact ae_of_all _ fun a => by
        dsimp only
        by_cases ha : N a=t
        · rw [Set.indicator_of_mem ha,if_pos ha]
        · rw [Set.indicator_of_notMem ha,if_neg ha]
    have hGcostI : Integrable Gcost (Ppre.prod Psuf) := by
      rw [←hsplit.map_eq]
      apply (integrable_map_measure hGcostM.aestronglyMeasurable hsplit.measurable.aemeasurable).2
      simpa only [Function.comp_def,hGcomp] using hPaySel
    have hGinner (b : Shao.Path t) :
        (∫ v,Gcost (v,b) ∂Ppre)=if b∈selectedSuffix then cost b else 0 := by
      dsimp only [Gcost]
      split_ifs <;> simp
    have hCostSelI : Integrable (fun b => if b∈selectedSuffix then cost b else 0) Psuf := by
      simpa only [hGinner] using hGcostI.integral_prod_right
    calc
      (∫ a,if N a=t then fromRank a else 0 ∂P)=
          ∫ a,if N a=t then Phi («prefix» a,suffix a) else 0 ∂P := by
        apply integral_congr_ae
        exact ae_of_all _ fun a => by
          dsimp only
          split_ifs with ha
          · exact (hPhiComp a ha).symm
          · rfl
      _ =∫ b,if b∈selectedSuffix then ∫ v,Phi (v,b) ∂Ppre else 0 ∂Psuf := hFubini.2.2.2
      _ ≤∫ b,if b∈selectedSuffix then cost b else 0 ∂Psuf := by
        apply integral_mono hFubini.2.2.1 hCostSelI
        intro b
        dsimp only
        split_ifs with hb
        · exact hSection b
        · rfl
      _ =∫ p,Gcost p ∂Ppre.prod Psuf := by
        rw [integral_prod_symm Gcost hGcostI]
        simp only [hGinner]
      _ =∫ a,if N a=t then payment a else 0 ∂P := by
        rw [←hsplit.map_eq,integral_map hsplit.measurable.aemeasurable hGcostM.aestronglyMeasurable]
        simp only [hGcomp]
  have hNmem (a : Shao.Path n) : N a∈Finset.Icc 1 L :=
    Finset.mem_Icc.2 ⟨(hRanks a).1.trans (hRanks a).2.1,(hRanks a).2.2.1⟩
  have hPartition (f : Shao.Path n → ℝ) (a : Shao.Path n) :
      (∑ t∈Finset.Icc 1 L,if N a=t then f a else 0)=f a := by
    calc
      (∑ t∈Finset.Icc 1 L,if N a=t then f a else 0)=
          (if N a=N a then f a else 0) := by
        apply Finset.sum_eq_single (N a)
        · intro t ht hne
          simp only [if_neg (Ne.symm hne)]
        · intro hnot
          exact False.elim (hnot (hNmem a))
      _=f a := if_pos rfl
  have hSelectedI (f : Shao.Path n → ℝ) (hf : Integrable f P) (t : ℕ) :
      Integrable (fun a => if N a=t then f a else 0) P := by
    have hi := hf.indicator (measurableSet_eq_fun hNM
      (measurable_const : Measurable (fun _ : Shao.Path n => t)))
    apply hi.congr
    exact ae_of_all _ fun a => by
      dsimp only
      by_cases ha : N a=t
      · rw [Set.indicator_of_mem ha,if_pos ha]
      · rw [Set.indicator_of_notMem ha,if_neg ha]
  have hRankBudget : (∫ a,fromRank a ∂P)≤∫ a,payment a ∂P := by
    have hri : Integrable fromRank P := hDi rank hrankN hrankM
    calc
      (∫ a,fromRank a ∂P)=∑ t∈Finset.Icc 1 L,∫ a,if N a=t then fromRank a else 0 ∂P := by
        rw [←integral_finsetSum _ (fun t ht => hSelectedI fromRank hri t)]
        apply integral_congr_ae
        exact ae_of_all _ fun a => (hPartition fromRank a).symm
      _ ≤∑ t∈Finset.Icc 1 L,∫ a,if N a=t then payment a else 0 ∂P :=
        Finset.sum_le_sum fun t ht => hSelected t ht
      _ =∫ a,payment a ∂P := by
        rw [←integral_finsetSum _ (fun t ht => hSelectedI payment hpaymenti t)]
        apply integral_congr_ae
        exact ae_of_all _ fun a => hPartition payment a
  have hPayBudget : (∫ a,payment a ∂P)≤240*CF*H/(n : ℝ) := by
    have hAdd1 : (∫ a,suffixMax a^2+suffixEnergy a ∂P)=
        (∫ a,suffixMax a^2 ∂P)+(∫ a,suffixEnergy a ∂P) := by
      simpa only [Pi.add_apply] using integral_add hJ2i hUi
    have hAdd2 : (∫ a,suffixMax a^2+suffixEnergy a+H ∂P)=
        (∫ a,suffixMax a^2+suffixEnergy a ∂P)+(∫ _ : Shao.Path n,H ∂P) := by
      simpa only [Pi.add_apply] using integral_add (hJ2i.add hUi) (integrable_const H)
    dsimp only [payment]
    rw [integral_const_mul,hAdd2,hAdd1,integral_const]
    simp only [probReal_univ,smul_eq_mul,one_mul]
    have hp := add_le_add hJb' hUb
    calc
      (2*CF/(n : ℝ))*((∫ a,suffixMax a^2 ∂P)+(∫ a,suffixEnergy a ∂P)+H)
        ≤(2*CF/(n : ℝ))*(112*H+7*H+H) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ =_ := by ring
  have hAdaptiveBudget : (∫ a,adaptive a ∂P)≤CT*H/(n : ℝ) := by
    have hei : Integrable (exceptional.indicator (fun _ : Shao.Path n => (1:ℝ))) P :=
      (integrable_const _).indicator hExceptionalM
    have hri : Integrable fromRank P := hDi rank hrankN hrankM
    have hExone : (∫ a,exceptional.indicator (fun _ : Shao.Path n => (1:ℝ)) a ∂P)=P.real exceptional := by
      change (∫ a,exceptional.indicator 1 a ∂P)=_
      exact integral_indicator_one hExceptionalM
    have hh := integral_mono (hDi tau0 htauN htauM) (hei.add hri) hPathDom
    simp only [Pi.add_apply] at hh
    rw [integral_add hei hri,hExone] at hh
    calc
      _ ≤12*H/(n : ℝ)+240*CF*H/(n : ℝ) :=
        hh.trans (add_le_add hExb (hRankBudget.trans hPayBudget))
      _ =CT*H/(n : ℝ) := by dsimp [CT]; ring
  let path : Shao.Path n×LabelPerm n → Shao.Path n := fun p => Spitzer.reorder p.1 p.2
  have hPathM : Measurable path := by
    apply measurable_from_prod_countable_left
    intro sigma
    exact Measurable.of_eval fun i => measurable_pi_apply (sigma i)
  have hEnergy (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.energy (Spitzer.reorder a sigma)=Shao.energy a := by
    simpa only [Shao.energy,Spitzer.reorder] using Equiv.sum_comp sigma (fun i => (a i)^2)
  have hSum (a : Shao.Path n) (sigma : LabelPerm n) :
      Shao.prefixSum (Spitzer.reorder a sigma) n=Shao.prefixSum a n := by
    simpa only [Shao.prefixSum_length,Spitzer.reorder] using Equiv.sum_comp sigma a
  have hId (a : Shao.Path n) : Spitzer.reorder a (Equiv.refl (Fin n))=a := rfl
  have hRem (a : Shao.Path n) (sigma : LabelPerm n) (j : ℕ) :
      remainingEnergy (Spitzer.reorder a sigma) j (Equiv.refl (Fin n))=
        remainingEnergy a j sigma := by
    unfold remainingEnergy
    rw [hEnergy]
    rfl
  have hWall (a : Shao.Path n) (sigma : LabelPerm n) :
      actualWall (Spitzer.reorder a sigma) x=actualWall a x := by
    unfold actualWall
    rw [hEnergy]
  have hAlive (a : Shao.Path n) (sigma : LabelPerm n) (j : ℕ) :
      sourceAlive I (Spitzer.reorder a sigma) x j (Equiv.refl (Fin n)) ↔
        sourceAlive I a x j sigma := by
    simp only [sourceAlive,hEnergy,hWall,hSum,hId]
  have hValue (a : Shao.Path n) (sigma : LabelPerm n) (j : ℕ) :
      sourceValue I F (Spitzer.reorder a sigma) x j (Equiv.refl (Fin n))=
        sourceValue I F a x j sigma := by
    simp only [sourceValue,hAlive,hWall,hSum,hRem,hId]
  have hCut (a : Shao.Path n) (sigma : LabelPerm n) :
      energyCutoff (Spitzer.reorder a sigma) H (Equiv.refl (Fin n))=
        energyCutoff a H sigma := by
    simp only [energyCutoff,hRem]
  have hTau (p : Shao.Path n×LabelPerm n) : tau0 (path p)=tau p := by
    dsimp only [tau0,tau,path]
    rw [hCut]
  have hPairEq : discrepancy=adaptive∘path := by
    ext p
    dsimp only [discrepancy,adaptive,D,d,terminal0,terminal,Function.comp_apply]
    simp only [hTau]
    simp only [path,hValue,hAlive]
  let X : Fin n → Shao.Path n → ℝ := fun i a => a i
  have hX (i : Fin n) : Measurable (X i) := measurable_pi_apply i
  have hLaw (i : Fin n) : IdentDistrib (X i) (id : ℝ → ℝ) P rho := by
    refine ⟨(hX i).aemeasurable,measurable_id.aemeasurable,?_⟩
    simpa only [Measure.map_id] using
      (measurePreserving_eval (μ := fun _ : Fin n => rho) i).map_eq
  have hIndep : iIndepFun X P :=
    iIndepFun_pi (X := fun _ : Fin n => (id : ℝ → ℝ))
      (fun _ => measurable_id.aemeasurable)
  have hMap : Measure.map path (revealLaw P)=P :=
    iid_randomPermutation_map_eq_pi P rho X hX hIndep hLaw
  have hPathLaw : IdentDistrib path (id : Shao.Path n → Shao.Path n) (revealLaw P) P :=
    ⟨hPathM.aemeasurable,measurable_id.aemeasurable,by simpa only [Measure.map_id] using hMap⟩
  have hAdaptiveM : Measurable adaptive := hDM tau0 htauN htauM
  have hAdaptiveI : Integrable adaptive P := hDi tau0 htauN htauM
  have hDiscrepancyM : Measurable discrepancy := by
    rw [hPairEq]
    exact hAdaptiveM.comp hPathM
  have hDiscrepancyI : Integrable discrepancy (revealLaw P) := by
    rw [hPairEq]
    exact (hPathLaw.comp hAdaptiveM).integrable_iff.mpr hAdaptiveI
  have hIntegralEq : (∫ p,discrepancy p ∂revealLaw P)=∫ a,adaptive a ∂P := by
    rw [hPairEq]
    exact (hPathLaw.comp hAdaptiveM).integral_eq
  have hHrelative : H/(n : ℝ)≤(8/3 : ℝ)*K*delta*Shao.standardNormalTail x := by
    have hp : (1+x)^3≤Real.exp (x^2) := by
      have hh : 1+x≤Real.exp x := by simpa only [add_comm] using Real.add_one_le_exp x
      have hp3 := pow_le_pow_left₀ (by linarith : (0:ℝ)≤1+x) hh 3
      have he : (Real.exp x)^3=Real.exp (3*x) := by
        rw [←Real.exp_nat_mul]
        congr 1
      exact (hp3.trans_eq he).trans (Real.exp_le_exp.2 (by nlinarith [sq_nonneg (x-16)]))
    have hScale : H/(n : ℝ)=K*delta*u*(1+x)^3 := by
      rw [hHratio]
      dsimp only [u]
      ring
    have hGauss := Shao.C2.AuxiliaryLowEnergyGaussian.auxiliary_exponential_le_gaussian_tail
      x (2*x^2) hx0.le (by nlinarith [sq_nonneg (x-1)])
    calc
      H/(n : ℝ)=K*delta*(u*(1+x)^3) := by rw [hScale]; ring
      _ ≤K*delta*(Real.exp (-3*x^2)*Real.exp (x^2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hu hp (by positivity) (Real.exp_pos _).le)
          (mul_nonneg hK.le hdelta.le)
      _ =K*delta*Real.exp (-(2*x^2)) := by
        rw [←Real.exp_add]
        congr 2
        ring
      _ ≤K*delta*((8/3 : ℝ)*Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hGauss (by positivity)
      _ =_ := by ring
  have hCTC : CT≤C := by
    dsimp [C]
    nlinarith [mul_nonneg hCT.le (mul_nonneg (by norm_num : (0:ℝ)≤8/3) hK.le)]
  have hNaturalBudget : (∫ p,discrepancy p ∂revealLaw P)≤CT*H/(n : ℝ) := by
    rw [hIntegralEq]
    exact hAdaptiveBudget
  refine ⟨hDiscrepancyM,hDiscrepancyI,?_,?_⟩
  · exact hNaturalBudget.trans
      (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hCTC hH.le) hnR.le)
  · calc
      _ ≤CT*H/(n : ℝ) := hNaturalBudget
      _ =CT*(H/(n : ℝ)) := by ring
      _ ≤CT*((8/3 : ℝ)*K*delta*Shao.standardNormalTail x) :=
        mul_le_mul_of_nonneg_left hHrelative hCT.le
      _ ≤C*delta*Shao.standardNormalTail x := by
        have hTail : 0≤delta*Shao.standardNormalTail x := by
          have hh : 0≤(8/3 : ℝ)*K*(delta*Shao.standardNormalTail x) :=
            (div_pos hH hnR).le.trans (by simpa only [mul_assoc] using hHrelative)
          exact nonneg_of_mul_nonneg_right hh (by positivity : 0<(8/3 : ℝ)*K)
        have hConst : CT*((8/3 : ℝ)*K)≤C := by dsimp [C]; nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hConst hTail]

end Shao.Probability.SourceActualAdaptiveTerminal
