import Shao.OQ4.RademacherScaleAssembly
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedTheorems : List Name := [
    `Shao.OQ4.RademacherScaleAssembly.DA2,
    `Shao.OQ4.RademacherScaleAssembly.DA2_subcritical]
  let expectedDefinitions : List Name := [
    `Shao.OQ4.RademacherScaleAssembly.eta3]
  let expectedOwned : List String := [
    "Shao.OQ4.RademacherScaleAssembly.DA2",
    "Shao.OQ4.RademacherScaleAssembly.DA2_subcritical",
    "Shao.OQ4.RademacherScaleAssembly.eta3",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.zero_of_abs_le",
    "Shao.OQ4.RademacherLatticeShift.delta.eq_1",
    "Shao.OQ4.RademacherScalarBounds.lambda.eq_1",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_1",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_2",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_3",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_4",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_5",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_6",
    "Shao.OQ4.RademacherScaleAssembly.DA2._simp_1_7",
    "Shao.OQ4.RademacherScaleAssembly.eta3.eq_1",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_1",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_2",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_3",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_4",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_5",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_6",
    "_private.Shao.OQ4.RademacherScaleAssembly.0.Shao.OQ4.RademacherScaleAssembly.cube_gap_bound._simp_1_7"]
  for name in expectedTheorems do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  for name in expectedDefinitions do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing public definition: {name}"
  let mut count : Nat := 0
  let mut definitionCount : Nat := 0
  let mut owned : List Name := []
  let mut ownedDefinitions : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao).isPrefixOf owner || (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf (privateToUserName name) then
      if info.isUnsafe || info.isPartial then throwError "Unsafe or partial selected declaration {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      count := count + 1
      let isDefinition := match info with | .defnInfo _ => true | _ => false
      if isDefinition then definitionCount := definitionCount + 1
      if owner == `Shao.OQ4.RademacherScaleAssembly then
        owned := name :: owned
        if isDefinition then ownedDefinitions := ownedDefinitions + 1
  unless owned.length == expectedOwned.length do throwError "Target actual owner count mismatch"
  for name in expectedOwned do
    unless owned.any (fun n => n.toString == name) do throwError "Expected target-owned declaration missing {name}"
  for name in owned do
    unless expectedOwned.contains name.toString do throwError "Unexpected target-owned declaration {name}"
  unless ownedDefinitions == expectedDefinitions.length do throwError "Target definition count mismatch"
  logInfo m!"OQ4_DA2_PARENT_PUBLIC_THEOREMS {expectedTheorems.length}"
  logInfo m!"OQ4_DA2_PARENT_PUBLIC_DEFINITIONS {expectedDefinitions.length}"
  logInfo m!"OQ4_DA2_PARENT_TARGET_OWNED {owned.length}"
  logInfo m!"OQ4_DA2_PARENT_PROJECT_RECORDS {count}"
  logInfo m!"OQ4_DA2_PARENT_PROJECT_DEFINITIONS {definitionCount}"
  logInfo m!"OQ4_DA2_PARENT_TARGET_DEFINITIONS {ownedDefinitions}"
