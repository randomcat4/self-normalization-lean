import Shao.OQ4.RademacherCorrectedBrownianBoundary
import Shao.OQ4.RademacherOriginalIIDTransport
import Shao.OQ4.RademacherOriginalStrictS4
import Shao.OQ4.StrictIIDWindow

set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology
universe uX uB

namespace Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary

private theorem source_weak_probability
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (hn : 0 < n) (h : ℝ) :
    μ.real (OriginalIIDWindow.sourceEvent n X (h / Real.sqrt (n : ℝ))) =
      RademacherS4Assembly.p n h := by
  rw [RademacherOriginalIIDTransport.source_probability_eq_product
    μ X hIndep hLaw n (h / Real.sqrt (n : ℝ))]
  have hsqrt : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn)).ne'
  have hsets : RademacherS5Assembly.selfNormalizedEvent n
      (h / Real.sqrt (n : ℝ)) =ᵐ[RademacherS5Assembly.pathLaw n]
      @Shao.closedStrip n h := by
    filter_upwards [(RademacherS5Assembly.actual_path_energy n).2] with a ha
    have hv : RademacherS5Assembly.V a = Real.sqrt (n : ℝ) := ha.2.2
    have hmul : (h / Real.sqrt (n : ℝ)) * RademacherS5Assembly.V a = h := by
      rw [hv]
      exact div_mul_cancel₀ h hsqrt
    simp only [RademacherS5Assembly.selfNormalizedEvent, Shao.closedStrip,
      Set.mem_setOf_eq, hmul]
  change ((RademacherS5Assembly.pathLaw n)
      (RademacherS5Assembly.selfNormalizedEvent n (h / Real.sqrt (n : ℝ)))).toReal =
    ((RademacherS5Assembly.pathLaw n) (@Shao.closedStrip n h)).toReal
  exact congrArg ENNReal.toReal (measure_congr hsets)

-- Proof: qualified original/product transport, actual_path_energy, sqrt n>0,
-- and almost-everywhere equality with the actual closedStrip.

private theorem source_strict_max_probability
    {ΩX : Type uX} [MeasurableSpace ΩX]
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law) (n : ℕ) (hn : 0 < n) (h : ℝ) :
    μ.real {ω | OriginalIIDWindow.sourceMaximum n X ω <
      (h / Real.sqrt (n : ℝ)) *
        Real.sqrt (OriginalIIDWindow.sourceEnergy n X ω)} =
      RademacherStrictCube.strictP n h := by
  rw [← StrictIIDWindow.source_strict_event_eq_max n hn X
    (h / Real.sqrt (n : ℝ))]
  exact RademacherOriginalStrictS4.source_strict_probability
    μ X hIndep hLaw n h

-- Proof: exact qualified deterministic positive-time max/prefix bridge,
-- then qualified original strict probability identity.

theorem original_weak_corrected_boundary
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law)
    (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < μ.real (OriginalIIDWindow.sourceEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.weakHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      μ.real (OriginalIIDWindow.sourceEvent (n_ k) X
        (h_ k / Real.sqrt (n_ k : ℝ))) /
      Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.weakHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  have hnpos : ∀ᶠ k : ℕ in atTop, 0 < n_ k := by
    filter_upwards [hscale2.eventually_gt_atTop (0 : ℝ)] with k hk
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.cast_zero, zero_div] at hk
    exact (lt_irrefl (0 : ℝ)) hk
  have hc := RademacherCorrectedBrownianBoundary.weak_corrected_boundary
    B P hB n_ h_ hh hscale2 hscale3
  refine ⟨?_, ?_⟩
  · filter_upwards [hnpos, hc.1] with k hk hp
    rw [source_weak_probability μ X hIndep hLaw (n_ k) hk (h_ k)]
    exact hp
  · apply hc.2.congr'
    filter_upwards [hnpos] with k hk
    rw [source_weak_probability μ X hIndep hLaw (n_ k) hk (h_ k)]

-- Proof: derive eventual n_>0 from hscale2; transfer qualified canonical
-- positivity and ratio limit by the first finite identity on that tail.

theorem original_strict_corrected_boundary
    {ΩX : Type uX} [MeasurableSpace ΩX]
    {ΩB : Type uB} [MeasurableSpace ΩB]
    (B : ℝ≥0 → ΩB → ℝ) (P : Measure ΩB) [IsProbabilityMeasure P]
    (hB : IsBrownianReal B P)
    (μ : Measure ΩX) [IsProbabilityMeasure μ] (X : ℕ → ΩX → ℝ)
    (hIndep : iIndepFun (fun i : ℕ => X (i + 1)) μ)
    (hLaw : ∀ i : ℕ, IdentDistrib (X (i + 1)) (id : ℝ → ℝ)
      μ RademacherCosine.law)
    (n_ : ℕ → ℕ) (h_ : ℕ → ℝ)
    (hh : Tendsto h_ atTop atTop)
    (hscale2 : Tendsto
      (fun k : ℕ => (n_ k : ℝ) / (h_ k) ^ 2) atTop atTop)
    (hscale3 : ∃ M : ℝ, 0 < M ∧
      ∃ K_M : ℕ, ∀ k : ℕ, K_M ≤ k →
        (n_ k : ℝ) / (h_ k) ^ 3 ≤ M) :
    (∀ᶠ k : ℕ in atTop,
      0 < μ.real {ω | OriginalIIDWindow.sourceMaximum (n_ k) X ω <
        (h_ k / Real.sqrt (n_ k : ℝ)) *
          Real.sqrt (OriginalIIDWindow.sourceEnergy (n_ k) X ω)} ∧
      0 < Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.strictHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) ∧
    Tendsto (fun k : ℕ =>
      μ.real {ω | OriginalIIDWindow.sourceMaximum (n_ k) X ω <
        (h_ k / Real.sqrt (n_ k : ℝ)) *
          Real.sqrt (OriginalIIDWindow.sourceEnergy (n_ k) X ω)} /
      Shao.Probability.BrownianSup.probability B P hB
        (RademacherCorrectedBrownianBoundary.strictHeight (h_ k) /
          Real.sqrt (n_ k : ℝ))) atTop (𝓝 (1 : ℝ)) := by
  have hnpos : ∀ᶠ k : ℕ in atTop, 0 < n_ k := by
    filter_upwards [hscale2.eventually_gt_atTop (0 : ℝ)] with k hk
    apply Nat.pos_of_ne_zero
    intro hz
    rw [hz, Nat.cast_zero, zero_div] at hk
    exact (lt_irrefl (0 : ℝ)) hk
  have hc := RademacherCorrectedBrownianBoundary.strict_corrected_boundary
    B P hB n_ h_ hh hscale2 hscale3
  refine ⟨?_, ?_⟩
  · filter_upwards [hnpos, hc.1] with k hk hp
    rw [source_strict_max_probability μ X hIndep hLaw (n_ k) hk (h_ k)]
    exact hp
  · apply hc.2.congr'
    filter_upwards [hnpos] with k hk
    rw [source_strict_max_probability μ X hIndep hLaw (n_ k) hk (h_ k)]

-- Proof: derive eventual n_>0 from hscale2; transfer qualified canonical
-- positivity and ratio limit by the second finite identity on that tail.

end Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary
end

/- Strict-window-necessity audit suffix adapted from mature accepted context189.
   Preparation only; first actual elaboration remains explicitly disabled.
   Capture the entire actual Source environment; no declaration namespace filtering. -/
open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  let main := env.header.mainModule
  unless main.toString == "Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary" do throwError "Unexpected main module {main}"
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
  let publicDefs : Array String := #[]
  let publicTheorems : Array String := #["Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary.original_weak_corrected_boundary", "Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary.original_strict_corrected_boundary"]
  let sourceInstances : Array String := #[]
  let publicNames := publicDefs ++ publicTheorems ++ sourceInstances
  let expectedPrivateDefs : Array String := #[]
  let expectedPrivateTheorems : Array String := #["Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary.source_weak_probability", "Shao.OQ4.RademacherOriginalCorrectedBrownianBoundary.source_strict_max_probability"]
  let expectedPrivate := expectedPrivateDefs ++ expectedPrivateTheorems
  let projectModuleNames : Array String := (env.header.moduleNames.filter (fun m => m.toString.startsWith "Shao." && m != main)).map Name.toString
  unless publicDefs.size == 0 && publicTheorems.size == 2 && sourceInstances.size == 0 && expectedPrivateDefs.size == 0 && expectedPrivateTheorems.size == 2 do throwError "Frozen audit inventory malformed"
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
  let outputDir := "/root/rivermind-data/shao-lean-20261021/workspaces/lead-oq4/repro_outputs/oq4-rademacher-original-corrected-brownian-boundary-check-v1/attempt001/"
  liftIO <| IO.FS.writeFile (outputDir ++ "audit-native.json") output.compress
  liftIO <| IO.FS.writeFile (outputDir ++ "raw-expressions.json") (Json.arr rawRows).compress
  liftIO <| IO.FS.writeFile (outputDir ++ "owned-interface.txt") actualInterface
  logInfo m!"ORIGINAL_CORRECTED_BROWNIAN_BOUNDARY_AUTHOR_NATIVE_MACHINE_PASS owned={difference.size} public={publicRows.size} explicitPrivate={explicitPrivate.size} generated={generated.size} closure={closureRows.size} projectDeclarations={projectRows.size}"
