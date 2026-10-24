import Shao.OQ4.RademacherS4Assembly
import Shao.OQ4.RademacherGeneralStrictS4
import Shao.OQ4.RademacherBrownianBoundaryShift
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
universe uB

namespace Shao.OQ4.RademacherCorrectedBrownianBoundary

def weakHeight (h : ℝ) : ℝ := (Nat.floor h : ℝ) + 1

def strictHeight (h : ℝ) : ℝ := (Nat.ceil h : ℝ)

private theorem inverse_square_remainder_bound (n : ℕ) (h d : ℝ)
    (hh : 0 < h) (hd0 : 0 ≤ d) (hd1 : d ≤ 1) :
    |(Real.pi ^ 2 / 8) *
        ((n : ℝ) / h ^ 2 - (n : ℝ) / (h + d) ^ 2) -
      (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * d| ≤
    (3 * (Real.pi ^ 2 / 8)) * ((n : ℝ) / h ^ 4) := by
  have hH : 0 < h + d := by linarith
  have hd2 : d ^ 2 ≤ 1 := by nlinarith
  have hratio : h * (3 * h + 2 * d) / (h + d) ^ 2 ≤ 3 := by
    apply (div_le_iff₀ (pow_pos hH 2)).2
    nlinarith [mul_nonneg hh.le hd0, sq_nonneg d]
  have hfactor : 0 ≤ h * (3 * h + 2 * d) / (h + d) ^ 2 := by positivity
  have hbound : d ^ 2 * (h * (3 * h + 2 * d) / (h + d) ^ 2) ≤ 3 :=
    (mul_le_of_le_one_left hfactor hd2).trans hratio
  have heq : (Real.pi ^ 2 / 8) *
        ((n : ℝ) / h ^ 2 - (n : ℝ) / (h + d) ^ 2) -
      (Real.pi ^ 2 / 4) * ((n : ℝ) / h ^ 3) * d =
      -(((Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 4)) *
        (d ^ 2 * (h * (3 * h + 2 * d) / (h + d) ^ 2))) := by
    field_simp [hh.ne', hH.ne'] <;> ring
  rw [heq, abs_neg, abs_of_nonneg (by positivity)]
  calc
    ((Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 4)) *
        (d ^ 2 * (h * (3 * h + 2 * d) / (h + d) ^ 2)) ≤
      ((Real.pi ^ 2 / 8) * ((n : ℝ) / h ^ 4)) * 3 :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (3 * (Real.pi ^ 2 / 8)) * ((n : ℝ) / h ^ 4) := by ring

-- Body of the preceding head: proof.md §3, exact identity (2), bound (3).

private theorem corrected_boundary_of_S4
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (n_ : ℕ → ℕ) (h_ H_ A_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M)
    (hwall : ∀ᶠ k : ℕ in atTop,
      h_ k ≤ H_ k ∧ H_ k ≤ h_ k + 1)
    (hApos : ∀ᶠ k : ℕ in atTop, 0 < A_ k)
    (hS4 : Tendsto (fun k : ℕ =>
      Real.log (A_ k /
        Shao.Probability.BrownianSup.probability B P hB
          (h_ k / Real.sqrt (n_ k : ℝ))) -
      (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) *
        (H_ k - h_ k)) atTop (𝓝 (0 : ℝ))) :
    (∀ᶠ k : ℕ in atTop,
      0 < A_ k ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (H_ k / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      A_ k / Shao.Probability.BrownianSup.probability B P hB
        (H_ k / Real.sqrt (n_ k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  let b : ℝ → ℝ := Shao.Probability.BrownianSup.probability B P hB
  let x : ℕ → ℝ := fun k => h_ k / Real.sqrt (n_ k : ℝ)
  let y : ℕ → ℝ := fun k => H_ k / Real.sqrt (n_ k : ℝ)
  let w : ℕ → ℝ := fun k =>
    (Real.pi ^ 2 / 4) * ((n_ k : ℝ) / (h_ k) ^ 3) * (H_ k - h_ k)
  let E : ℕ → ℝ := fun k => (Real.pi ^ 2 / 8) *
    ((n_ k : ℝ) / (h_ k) ^ 2 - (n_ k : ℝ) / (H_ k) ^ 2)
  have hlegal : ∀ᶠ k : ℕ in atTop,
      1 ≤ h_ k ∧ 0 < Real.sqrt (n_ k : ℝ) ∧
      (Real.sqrt (n_ k : ℝ)) ^ 2 = (n_ k : ℝ) := by
    filter_upwards [hh.eventually_ge_atTop (1 : ℝ),
      hscale2.eventually_ge_atTop (1 : ℝ)] with k hk ht
    have hh0 : 0 < h_ k := by linarith
    have hn : 0 < (n_ k : ℝ) := by
      have hsq : (h_ k) ^ 2 ≤ (n_ k : ℝ) := by
        simpa only [one_mul] using (le_div_iff₀ (pow_pos hh0 2)).mp ht
      exact lt_of_lt_of_le (pow_pos hh0 2) hsq
    exact ⟨hk, Real.sqrt_pos.2 hn, Real.sq_sqrt hn.le⟩
  have hxpos : ∀ᶠ k : ℕ in atTop, 0 < x k := by
    filter_upwards [hlegal] with k hk
    exact div_pos (by linarith [hk.1]) hk.2.1
  have hypos : ∀ᶠ k : ℕ in atTop, 0 < y k := by
    filter_upwards [hlegal, hwall] with k hk hw
    exact div_pos (by linarith [hk.1, hw.1]) hk.2.1
  have hx : Tendsto x atTop (𝓝 (0 : ℝ)) := by
    apply Metric.tendsto_atTop.2
    intro ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.1
      (hlegal.and (hscale2.eventually_ge_atTop (1 / ε ^ 2 + 1)))
    refine ⟨K, fun k hk => ?_⟩
    rcases hK k hk with ⟨hl, ht⟩
    have hh0 : 0 < h_ k := by linarith [hl.1]
    have ht' : 1 / ε ^ 2 < (n_ k : ℝ) / (h_ k) ^ 2 := by linarith
    have hs : (h_ k) ^ 2 < (ε * Real.sqrt (n_ k : ℝ)) ^ 2 := by
      rw [mul_pow, hl.2.2]
      have ht'' := (div_lt_div_iff₀ (pow_pos hε 2) (pow_pos hh0 2)).mp ht'
      simpa only [one_mul, mul_one, mul_comm] using ht''
    have hxlt : x k < ε := by
      apply (div_lt_iff₀ hl.2.1).2
      exact (sq_lt_sq₀ hh0.le (mul_pos hε hl.2.1).le).mp hs
    rw [Real.dist_eq, sub_zero, abs_of_pos (div_pos hh0 hl.2.1)]
    exact hxlt
  have hy : Tendsto y atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' (hypos.mono fun _ hk => hk.le) ?_
      (by simpa only [mul_zero] using hx.const_mul 2)
    filter_upwards [hlegal, hwall] with k hk hw
    change H_ k / Real.sqrt (n_ k : ℝ) ≤
      2 * (h_ k / Real.sqrt (n_ k : ℝ))
    calc
      H_ k / Real.sqrt (n_ k : ℝ) ≤
          (2 * h_ k) / Real.sqrt (n_ k : ℝ) :=
        div_le_div_of_nonneg_right (by linarith [hk.1, hw.2]) hk.2.1.le
      _ = 2 * (h_ k / Real.sqrt (n_ k : ℝ)) := by ring
  have hshift := RademacherBrownianBoundaryShift.actual_brownian_boundary_shift
    B P hB x y hx hy hxpos hypos
  have hblog : Tendsto (fun k : ℕ => Real.log (b (y k) / b (x k)) - E k)
      atTop (𝓝 (0 : ℝ)) := by
    apply hshift.2.1.congr'
    filter_upwards [hlegal, hwall] with k hk hw
    have heq (z : ℝ) :
        1 / (z / Real.sqrt (n_ k : ℝ)) ^ 2 = (n_ k : ℝ) / z ^ 2 := by
      rw [div_pow, one_div_div, hk.2.2]
    dsimp only [x, y, b, E]
    rw [heq, heq]
  obtain ⟨M, hM, KM, hKM⟩ := hscale3
  have hMlim : Tendsto (fun k : ℕ => M / h_ k) atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hh).const_mul M
  have hfour : Tendsto (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 4)
      atTop (𝓝 (0 : ℝ)) := by
    apply squeeze_zero' ?_ ?_ hMlim
    · exact Eventually.of_forall fun k => div_nonneg (Nat.cast_nonneg _) (by positivity)
    · filter_upwards [hlegal, eventually_ge_atTop KM] with k hk hkm
      have hh0 : 0 < h_ k := by linarith [hk.1]
      calc
        (n_ k : ℝ) / (h_ k) ^ 4 = ((n_ k : ℝ) / (h_ k) ^ 3) / h_ k := by ring
        _ ≤ M / h_ k := div_le_div_of_nonneg_right (hKM k hkm) hh0.le
  have hR : Tendsto (fun k : ℕ => E k - w k) atTop (𝓝 (0 : ℝ)) := by
    apply (tendsto_zero_iff_abs_tendsto_zero _).2
    apply squeeze_zero' (Eventually.of_forall fun k => abs_nonneg (E k - w k)) ?_
      (by simpa only [mul_zero] using hfour.const_mul (3 * (Real.pi ^ 2 / 8)))
    filter_upwards [hlegal, hwall] with k hk hw
    have hh0 : 0 < h_ k := by linarith [hk.1]
    have hbound := inverse_square_remainder_bound (n_ k) (h_ k) (H_ k - h_ k)
      hh0 (by linarith [hw.1]) (by linarith [hw.2])
    simpa only [add_sub_cancel] using hbound
  have hs4 : Tendsto (fun k : ℕ => Real.log (A_ k / b (x k)) - w k)
      atTop (𝓝 (0 : ℝ)) := hS4
  have hlog : Tendsto (fun k : ℕ => Real.log (A_ k / b (y k)))
      atTop (𝓝 (0 : ℝ)) := by
    have hsum := (hs4.sub hblog).sub hR
    have heq : (fun k : ℕ =>
        (Real.log (A_ k / b (x k)) - w k) -
        (Real.log (b (y k) / b (x k)) - E k) - (E k - w k)) =ᶠ[atTop]
        (fun k : ℕ => Real.log (A_ k / b (y k))) := by
      filter_upwards [hApos, hshift.1] with k ha hb
      rw [Real.log_div ha.ne' hb.1.ne',
        Real.log_div hb.2.1.ne' hb.1.ne', Real.log_div ha.ne' hb.2.1.ne']
      ring
    simpa only [sub_self, sub_zero] using hsum.congr' heq
  have hpositive : ∀ᶠ k : ℕ in atTop, 0 < A_ k ∧ 0 < b (y k) := by
    filter_upwards [hApos, hshift.1] with k ha hb
    exact ⟨ha, hb.2.1⟩
  refine ⟨hpositive, ?_⟩
  have hexp := (Real.continuous_exp.tendsto (0 : ℝ)).comp hlog
  have heqexp : (fun k : ℕ => Real.exp (Real.log (A_ k / b (y k)))) =ᶠ[atTop]
      (fun k : ℕ => A_ k / b (y k)) := by
    filter_upwards [hpositive] with k hk
    exact Real.exp_log (div_pos hk.1 hk.2)
  simpa only [Real.exp_zero, Function.comp_def] using hexp.congr' heqexp

-- Body of the preceding head: proof.md §§2--4. The log residual is established
-- as an internal have; the theorem returns only positivity and the ratio.
-- A_ is instantiated with an actual qualified finite probability in BOTH
-- public wrappers below. hS4 is never a new public probability hypothesis.

theorem weak_corrected_boundary
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < RademacherS4Assembly.p (n_ k) (h_ k) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (weakHeight (h_ k) / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      RademacherS4Assembly.p (n_ k) (h_ k) /
        Shao.Probability.BrownianSup.probability B P hB
          (weakHeight (h_ k) / Real.sqrt (n_ k : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  let m : ℕ → ℕ := fun k => Nat.floor (h_ k)
  have hgeom : ∀ᶠ k : ℕ in atTop,
      1 ≤ m k ∧ (m k : ℝ) ≤ h_ k ∧ h_ k < (m k : ℝ) + 1 := by
    filter_upwards [hh.eventually_ge_atTop (2 : ℝ)] with k hk
    exact ⟨Nat.floor_pos.mpr (by linarith),
      Nat.floor_le (by linarith), Nat.lt_floor_add_one _⟩
  have hcell := eventually_atTop.1 hgeom
  have hs := RademacherS4Assembly.S4_EVENTUAL B P hB m n_ h_
    hcell hh hscale2 hscale3
  rcases hs with ⟨_, _, _, _, _, _, _, hwlog, _, Kt, Kp, _, _, hprob, _⟩
  have hApos : ∀ᶠ k : ℕ in atTop, 0 < RademacherS4Assembly.p (n_ k) (h_ k) := by
    filter_upwards [eventually_ge_atTop Kp] with k hk
    rcases (hprob k hk).1 with ⟨_, _, _, _, _, _, _, _, _, hp, _⟩
    exact hp
  have hwall : ∀ᶠ k : ℕ in atTop,
      h_ k ≤ weakHeight (h_ k) ∧ weakHeight (h_ k) ≤ h_ k + 1 := by
    filter_upwards [hgeom] with k hk
    change h_ k ≤ (m k : ℝ) + 1 ∧ (m k : ℝ) + 1 ≤ h_ k + 1
    exact ⟨hk.2.2.le, by linarith [hk.2.1]⟩
  exact corrected_boundary_of_S4 B P hB n_ h_ (fun k => weakHeight (h_ k))
    (fun k => RademacherS4Assembly.p (n_ k) (h_ k)) hh hscale2 hscale3 hwall hApos hwlog

-- Body of the preceding head: proof.md §5. Obtain floor-cell S4_EVENTUAL,
-- its log residual, and actual p positivity, then instantiate the helper.

theorem strict_corrected_boundary
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P) (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (strictHeight (h_ k) / Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      RademacherStrictCube.strictP (n_ k) (h_ k) /
        Shao.Probability.BrownianSup.probability B P hB
          (strictHeight (h_ k) / Real.sqrt (n_ k : ℝ)))
      atTop (𝓝 (1 : ℝ)) := by
  have hs := RademacherGeneralStrictS4.strict_S4_EVENTUAL B P hB n_ h_
    hh hscale2 hscale3
  have hApos : ∀ᶠ k : ℕ in atTop,
      0 < RademacherStrictCube.strictP (n_ k) (h_ k) := hs.1.mono fun _ hk => hk.1
  have hwall : ∀ᶠ k : ℕ in atTop,
      h_ k ≤ strictHeight (h_ k) ∧ strictHeight (h_ k) ≤ h_ k + 1 := by
    filter_upwards [hh.eventually_ge_atTop (1 : ℝ)] with k hk
    have hb := RademacherRealStrictBoundary.ceil_boundary_bridge
      (n_ k) (h_ k) (by linarith)
    change h_ k ≤ (Nat.ceil (h_ k) : ℝ) ∧ (Nat.ceil (h_ k) : ℝ) ≤ h_ k + 1
    exact ⟨hb.2.2.2.1, by linarith [hb.2.1, hb.2.2.1]⟩
  exact corrected_boundary_of_S4 B P hB n_ h_ (fun k => strictHeight (h_ k))
    (fun k => RademacherStrictCube.strictP (n_ k) (h_ k))
    hh hscale2 hscale3 hwall hApos hs.2.1

-- Body of the preceding head: proof.md §6. Obtain strict_S4_EVENTUAL,
-- unfold only its Q/correction/delta and strictHeight, instantiate helper.

end Shao.OQ4.RademacherCorrectedBrownianBoundary
end

/- Strict-window-necessity audit suffix adapted from mature accepted context189.
   Preparation only; first actual elaboration remains explicitly disabled.
   Capture the entire actual Source environment; no declaration namespace filtering. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  let main := env.header.mainModule
  unless main.toString == "Shao.OQ4.RademacherCorrectedBrownianBoundary" do throwError "Unexpected main module {main}"
  unless env.header.trustLevel == 1025 do throwError "Unexpected trust level {env.header.trustLevel}"
  if Lean.debug.skipKernelTC.get opts then throwError "Kernel type checking was skipped"
  if opts.getBool ("autoImplicit".toName) true then throwError "autoImplicit must be false"
  let sorted := fun (ns : Array Name) => ns.qsort (fun a b => a.toString < b.toString)
  let all := env.constants.toList
  let difference := sorted <| (all.filter fun (n, _) => !(env.constants.map₁.contains n)).toArray.map Prod.fst
  let ownership := sorted <| (all.filter fun (n, _) => (env.getModuleIdxFor? n).isNone).toArray.map Prod.fst
  let stage2 := sorted <| env.constants.foldStage2 (fun ns n _ => ns.push n) (#[] : Array Name)
  unless difference == ownership && ownership == stage2 do throwError "Difference/ownership/stage2 disagree"
  let ownerOf := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]!
    | none => main
  let kindOf := fun (i : ConstantInfo) =>
    match i with
    | .axiomInfo _ => "axiom"
    | .defnInfo _ => "definition"
    | .thmInfo _ => "theorem"
    | .opaqueInfo _ => "opaque"
    | .quotInfo _ => "quotient"
    | .inductInfo _ => "inductive"
    | .ctorInfo _ => "constructor"
    | .recInfo _ => "recursor"
  let namesJson := fun (ns : Array Name) => Json.arr (ns.map fun n => toJson n.toString)
  let allowedAxioms : Array String := #["propext", "Classical.choice", "Quot.sound"]
  let publicDefs : Array String := #["Shao.OQ4.RademacherCorrectedBrownianBoundary.weakHeight", "Shao.OQ4.RademacherCorrectedBrownianBoundary.strictHeight"]
  let publicTheorems : Array String := #["Shao.OQ4.RademacherCorrectedBrownianBoundary.weak_corrected_boundary", "Shao.OQ4.RademacherCorrectedBrownianBoundary.strict_corrected_boundary"]
  let sourceInstances : Array String := #[]
  let publicNames := publicDefs ++ publicTheorems ++ sourceInstances
  let expectedPrivateDefs : Array String := #[]
  let expectedPrivateTheorems : Array String := #["Shao.OQ4.RademacherCorrectedBrownianBoundary.inverse_square_remainder_bound", "Shao.OQ4.RademacherCorrectedBrownianBoundary.corrected_boundary_of_S4"]
  let expectedPrivate := expectedPrivateDefs ++ expectedPrivateTheorems
  let projectModuleNames : Array String := (env.header.moduleNames.filter (fun m => m.toString.startsWith "Shao." && m != main)).map Name.toString
  unless publicDefs.size == 2 && publicTheorems.size == 2 && sourceInstances.size == 0 && expectedPrivateDefs.size == 0 && expectedPrivateTheorems.size == 2 do throwError "Frozen audit inventory malformed"
  for s in publicNames do
    let n := s.toName
    unless difference.contains n do throwError "Missing owned frozen public {n}"
    let some ci := env.find? n | throwError "Missing declaration {n}"
    if publicDefs.contains s then
      unless kindOf ci == "definition" do throwError "Expected transparent definition {n}"
    else if publicTheorems.contains s then
      unless ci.isTheorem do throwError "Expected theorem {n}"
    else
      unless kindOf ci == "definition" || kindOf ci == "opaque" || kindOf ci == "theorem" do
        throwError "Unexpected source-instance native kind {n}"
  let mut explicitPrivate : Array Name := #[]
  let mut explicitPrivateMapping : Array Json := #[]
  for s in expectedPrivate do
    let found := difference.filter fun n => (privateToUserName? n).getD n == s.toName
    unless found.size == 1 do throwError "Expected exactly one actual private declaration for {s}"
    let n := found[0]!
    let some ci := env.find? n | throwError "Missing private declaration {n}"
    let observedKind := kindOf ci
    if expectedPrivateDefs.contains s then
      unless observedKind == "definition" do throwError "Expected private transparent definition {n}; observed kind={observedKind}"
    else
      unless ci.isTheorem do throwError "Expected private theorem {n}; observed kind={observedKind}"
    explicitPrivate := explicitPrivate.push n
    explicitPrivateMapping := explicitPrivateMapping.push <| Json.mkObj [("frozenUserName",toJson s),("actualName",toJson n.toString),("actualKind",toJson observedKind)]
  -- Every actual owned type and every transparent definition value is exported fully.
  let ppExplicit : Expr → CommandElabM String := fun e => do
    let fmt ← liftTermElabM <| withOptions (fun o =>
      ((((o.setBool ("pp.all".toName) true).setBool ("pp.proofs".toName) true).setBool ("pp.deepTerms".toName) true).set ("pp.maxDepth".toName) (1000000 : Nat)).set ("pp.maxSteps".toName) (100000000 : Nat)) (Meta.ppExpr e)
    return fmt.pretty 120
  -- Bounded NEW-OWNED dependency closure, seeded by the exact named source
  -- instance. This is NOT a registered-instance classification. Foreign refs
  -- are filtered before enqueueing; no old-only closure is added here.
  let mut ownedReferenceRows : Array (Name × Array Name) := #[]
  for n in difference do
    let some ci := env.find? n | throwError "Missing owned dependency source {n}"
    let cv := ci.value? true
    let vr := cv.map (·.getUsedConstants) |>.getD #[]
    let refs := ci.type.getUsedConstants ++ vr
    ownedReferenceRows := ownedReferenceRows.push
      (n, refs.filter fun dep => difference.contains dep)
  let mut instancePending := sourceInstances.map String.toName
  let mut sourceInstanceOwnedClosure : Array Name := #[]
  while !instancePending.isEmpty do
    let n := instancePending.back!
    instancePending := instancePending.pop
    unless sourceInstanceOwnedClosure.contains n do
      unless difference.contains n do throwError "Non-owned source-instance closure node {n}"
      sourceInstanceOwnedClosure := sourceInstanceOwnedClosure.push n
      let some (_, refs) := ownedReferenceRows.find? (fun row => row.1 == n)
        | throwError "Missing precomputed owned refs {n}"
      instancePending := instancePending ++ refs
  unless sourceInstanceOwnedClosure.size ≤ difference.size do
    throwError "Source-instance closure exceeded the actual owned environment"

  let mut directOwnedReferences : NameSet := {}
  let mut ownedRows : Array Json := #[]
  let mut rawRows : Array Json := #[]
  let mut publicRows : Array Json := #[]
  let mut sourceInstanceActualMapping : Array Json := #[]
  let mut actualInterface := "Actual sparse-strict-critical-denominator owned interface: unfiltered environment difference\n"
  for n in difference do
    let some ci := env.find? n | throwError "Missing owned {n}"
    let ax ← Lean.collectAxioms n
    if ci.isUnsafe || ci.isPartial || kindOf ci == "axiom" then throwError "Unsafe/partial/new owned axiom {n}"
    for a in ax do
      unless allowedAxioms.contains a.toString do throwError "Disallowed axiom {a} in {n}"
    let ty ← ppExplicit ci.type
    let val ← match ci with | .defnInfo d => ppExplicit d.value | _ => pure ""
    let opaqueVal ← match ci with | .opaqueInfo d => ppExplicit d.value | _ => pure ""
    let tr := ci.type.getUsedConstants
    let cv := ci.value? true
    let vr := cv.map (·.getUsedConstants) |>.getD #[]
    let sourceInstance := sourceInstances.contains n.toString
    let instanceOwnedDependency := sourceInstanceOwnedClosure.contains n
    let propValued ← liftTermElabM <| Meta.isProp ci.type
    let fullVal ←
      if !ci.isTheorem || instanceOwnedDependency then
        match cv with
        | some value => ppExplicit value
        | none => pure ""
      else pure ""
    if sourceInstance then
      sourceInstanceActualMapping := sourceInstanceActualMapping.push <| Json.mkObj [("frozenUserName",toJson n.toString),("actualName",toJson n.toString),("actualKind",toJson (kindOf ci)),("typeIsProp",toJson propValued),("valueAvailable",toJson cv.isSome),("fullAvailableValue",toJson fullVal)]
    for dep in (tr ++ vr) do directOwnedReferences := directOwnedReferences.insert dep
    if kindOf ci == "opaque" && cv.isNone then throwError "Owned opaque value unavailable {n}"
    let row := Json.mkObj [
      ("name",toJson n.toString),("module",toJson (ownerOf n).toString),("kind",toJson (kindOf ci)),
      ("unsafe",toJson ci.isUnsafe),("partial",toJson ci.isPartial),("axioms",namesJson ax),
      ("type",toJson ty),("elaboratedTypeExplicit",toJson ty),("definitionValue",toJson val),
      ("elaboratedValueExplicit",toJson val),("opaqueValueExplicit",toJson opaqueVal),
      ("typeRefs",namesJson tr),("valueRefs",namesJson vr),("valueAvailable",toJson cv.isSome),
      ("typeIsProp",toJson propValued),("sourceInstance",toJson sourceInstance),("sourceInstanceOwnedDependencyClosureMember",toJson instanceOwnedDependency),("fullAvailableValue",toJson fullVal),
      ("public",toJson (publicNames.contains n.toString)),("explicitPrivate",toJson (explicitPrivate.contains n))]
    ownedRows := ownedRows.push row
    rawRows := rawRows.push <| Json.mkObj [
      ("name",toJson n.toString),("typeExpr",toJson (reprStr ci.type)),
      ("definitionExpr",toJson (match ci with | .defnInfo d => reprStr d.value | _ => "")),
      ("opaqueExpr",toJson (match ci with | .opaqueInfo d => reprStr d.value | _ => "")),
      ("sourceInstanceOwnedDependencyValueExpr",toJson (if instanceOwnedDependency then (cv.map reprStr).getD "" else ""))]
    actualInterface := actualInterface ++ "\n===== " ++ n.toString ++ " [" ++ kindOf ci ++ "] =====\nTYPE\n" ++ ty ++
      (if kindOf ci == "definition" then "\nFULL DEFINITION VALUE\n" ++ val else "") ++
      (if kindOf ci == "opaque" then "\nFULL OPAQUE VALUE\n" ++ opaqueVal else "") ++
      (if instanceOwnedDependency then "\nFULL SOURCE INSTANCE OWNED DEPENDENCY VALUE\n" ++ fullVal else "") ++ "\n"
    if publicNames.contains n.toString then publicRows := publicRows.push row
  -- Follow every actual type AND value; opaque bodies are requested explicitly.
  -- Project classification uses module ownership, never declaration-name prefixes.
  let mut pending := difference
  let mut seen : NameSet := {}
  let mut closureRows : Array Json := #[]
  let mut oldDirectInterfaces : Array Json := #[]
  let mut projectRows : Array Json := #[]
  let mut projectModules : Array Name := #[]
  let mut closureAxioms : Array Name := #[]
  while !pending.isEmpty do
    let n := pending.back!
    pending := pending.pop
    unless seen.contains n do
      seen := seen.insert n
      let some ci := env.find? n | throwError "Missing transitive dependency {n}"
      let tr := ci.type.getUsedConstants
      let cv := ci.value? true
      let vr := cv.map (·.getUsedConstants) |>.getD #[]
      if kindOf ci == "opaque" && cv.isNone then throwError "Transitive opaque value unavailable {n}"
      pending := pending ++ tr ++ vr
      let owner := ownerOf n
      if ci.isUnsafe || ci.isPartial then throwError "Unsafe/partial transitive dependency {n}"
      if kindOf ci == "axiom" then
        unless allowedAxioms.contains n.toString do throwError "Disallowed transitive axiom {n}"
        closureAxioms := closureAxioms.push n
      closureRows := closureRows.push <| Json.mkObj [
        ("name",toJson n.toString),("module",toJson owner.toString),("kind",toJson (kindOf ci)),
        ("unsafe",toJson ci.isUnsafe),("partial",toJson ci.isPartial),
        ("typeRefs",namesJson tr),("valueRefs",namesJson vr),("valueAvailable",toJson cv.isSome)]
      if owner != main && directOwnedReferences.contains n then
        let oldType ← ppExplicit ci.type
        let oldValue ← match ci with
          | .defnInfo d => ppExplicit d.value
          | .opaqueInfo d => ppExplicit d.value
          | _ => pure ""
        let oldAx ← Lean.collectAxioms n
        oldDirectInterfaces := oldDirectInterfaces.push <| Json.mkObj [
          ("name",toJson n.toString),("module",toJson owner.toString),("kind",toJson (kindOf ci)),
          ("directlyConsumedByOwned",toJson true),("elaboratedTypeExplicit",toJson oldType),
          ("fullAvailableNonTheoremValue",toJson oldValue),("valueAvailable",toJson cv.isSome),
          ("theoremProofQualificationReused",toJson ci.isTheorem),("axioms",namesJson oldAx),
          ("typeRefs",namesJson tr),("valueRefs",namesJson vr)]
      if projectModuleNames.contains owner.toString then
        let ax ← Lean.collectAxioms n
        if kindOf ci == "axiom" then throwError "Project axiom-kind declaration {n}"
        for a in ax do
          unless allowedAxioms.contains a.toString do throwError "Disallowed project axiom {a} in {n}"
        unless projectModules.contains owner do projectModules := projectModules.push owner
        let directlyConsumed := directOwnedReferences.contains n
        let oldType ← if directlyConsumed then ppExplicit ci.type else pure ""
        let oldDefinitionValue ← match ci with
          | .defnInfo d => if directlyConsumed then ppExplicit d.value else pure ""
          | _ => pure ""
        let oldOpaqueValue ← match ci with
          | .opaqueInfo d => if directlyConsumed then ppExplicit d.value else pure ""
          | _ => pure ""
        projectRows := projectRows.push <| Json.mkObj [
          ("directlyConsumedByOwned",toJson directlyConsumed),("elaboratedTypeExplicit",toJson oldType),
          ("definitionValue",toJson oldDefinitionValue),("opaqueValueExplicit",toJson oldOpaqueValue),
          ("name",toJson n.toString),("module",toJson owner.toString),("kind",toJson (kindOf ci)),
          ("unsafe",toJson ci.isUnsafe),("partial",toJson ci.isPartial),("axioms",namesJson ax),
          ("typeRefs",namesJson tr),("valueRefs",namesJson vr),("valueAvailable",toJson cv.isSome)]
      else if owner != main && owner.toString.startsWith "Shao." then
        throwError "Unbound project dependency module {owner} for {n}"
  let importedProject := sorted <| env.header.moduleNames.filter (fun m => m.toString.startsWith "Shao." && m != main)
  let mut resolvedImports : Array Json := #[]
  for m in importedProject do
    unless projectModuleNames.contains m.toString do throwError "Unexpected project import {m}"
    let path ← liftIO <| Lean.findOLean m
    resolvedImports := resolvedImports.push <| Json.mkObj [("module",toJson m.toString),("path",toJson path.toString)]
  unless importedProject.size ≤ projectModuleNames.size do throwError "Actual project imports exceed the recorded binding inventory"
  let mut allResolvedImports : Array Json := #[]
  for m in sorted (env.header.moduleNames.filter (fun m => m != main)) do
    let path ← liftIO <| Lean.findOLean m
    allResolvedImports := allResolvedImports.push <| Json.mkObj [("module",toJson m.toString),("path",toJson path.toString)]
  let generated := difference.filter fun n => !publicNames.contains n.toString && !explicitPrivate.contains n
  let output := Json.mkObj [
    ("status",toJson "NATIVE_MACHINE_PASS"),("mainModule",toJson main.toString),
    ("trustLevel",toJson env.header.trustLevel.toNat),("skipKernelTC",toJson (Lean.debug.skipKernelTC.get opts)),
    ("autoImplicit",toJson (opts.getBool ("autoImplicit".toName) true)),
    ("environmentDifference",namesJson difference),("moduleOwnership",namesJson ownership),("stage2",namesJson stage2),
    ("owned",Json.arr ownedRows),("public",Json.arr publicRows),("explicitPrivate",namesJson (sorted explicitPrivate)),
    ("actualGenerated",namesJson generated),("actualGeneratedCount",toJson generated.size),
    ("explicitPrivateMapping",Json.arr explicitPrivateMapping),("sourceInstanceActualMapping",Json.arr sourceInstanceActualMapping),
    ("oldDirectInterfaces",Json.arr oldDirectInterfaces),
    ("sourceInstanceOwnedDependencyClosure",namesJson (sorted sourceInstanceOwnedClosure)),
    ("sourceInstanceOwnedDependencyClosureMeaning",toJson "Conservative source-instance-owned dependency closure; NOT registered-instance classification"),
    ("closure",Json.arr closureRows),("closureAxioms",namesJson (sorted closureAxioms)),
    ("projectDependencies",Json.arr projectRows),("projectModules",namesJson (sorted projectModules)),
    ("importedProjectModules",namesJson importedProject),("resolvedImports",Json.arr resolvedImports),("allResolvedImports",Json.arr allResolvedImports),
    ("actualInterfaceReviewPending",toJson true)]
  let outputDir := "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-corrected-brownian-boundary-check-v1/attempt002/"
  liftIO <| IO.FS.writeFile (outputDir ++ "audit-native.json") output.compress
  liftIO <| IO.FS.writeFile (outputDir ++ "raw-expressions.json") (Json.arr rawRows).compress
  liftIO <| IO.FS.writeFile (outputDir ++ "owned-interface.txt") actualInterface
  logInfo m!"CORRECTED_BROWNIAN_BOUNDARY_AUTHOR_NATIVE_MACHINE_PASS owned={difference.size} public={publicRows.size} explicitPrivate={explicitPrivate.size} generated={generated.size} closure={closureRows.size} projectDeclarations={projectRows.size}"
