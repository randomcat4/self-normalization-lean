import Shao.OQ4.RademacherS2Assembly
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedTheorems : List Name := [
    `Shao.OQ4.RademacherS2Assembly.definition_bridges,
    `Shao.OQ4.RademacherS2Assembly.F0,
    `Shao.OQ4.RademacherS2Assembly.F0_zero_time,
    `Shao.OQ4.RademacherS2Assembly.F0_small_cells,
    `Shao.OQ4.RademacherS2Assembly.T0,
    `Shao.OQ4.RademacherS2Assembly.F1,
    `Shao.OQ4.RademacherS2Assembly.Q1]
  let expectedDefinitions : List Name := [
    `Shao.OQ4.RademacherS2Assembly.H,
    `Shao.OQ4.RademacherS2Assembly.N,
    `Shao.OQ4.RademacherS2Assembly.t,
    `Shao.OQ4.RademacherS2Assembly.a,
    `Shao.OQ4.RademacherS2Assembly.rho,
    `Shao.OQ4.RademacherS2Assembly.eps,
    `Shao.OQ4.RademacherS2Assembly.q,
    `Shao.OQ4.RademacherS2Assembly.R,
    `Shao.OQ4.RademacherS2Assembly.B,
    `Shao.OQ4.RademacherS2Assembly.p,
    `Shao.OQ4.RademacherS2Assembly.K,
    `Shao.OQ4.RademacherS2Assembly.D,
    `Shao.OQ4.RademacherS2Assembly.C_U]
  let expectedOwned : List Name := [
    `Shao.OQ4.RademacherS2Assembly.B,
    `Shao.OQ4.RademacherS2Assembly.C_U,
    `Shao.OQ4.RademacherS2Assembly.D,
    `Shao.OQ4.RademacherS2Assembly.F0,
    `Shao.OQ4.RademacherS2Assembly.F0_small_cells,
    `Shao.OQ4.RademacherS2Assembly.F0_zero_time,
    `Shao.OQ4.RademacherS2Assembly.F1,
    `Shao.OQ4.RademacherS2Assembly.H,
    `Shao.OQ4.RademacherS2Assembly.K,
    `Shao.OQ4.RademacherS2Assembly.N,
    `Shao.OQ4.RademacherS2Assembly.Q1,
    `Shao.OQ4.RademacherS2Assembly.R,
    `Shao.OQ4.RademacherS2Assembly.T0,
    `Shao.OQ4.RademacherS2Assembly.a,
    `Shao.OQ4.RademacherS2Assembly.definition_bridges,
    `Shao.OQ4.RademacherS2Assembly.eps,
    `Shao.OQ4.RademacherS2Assembly.p,
    `Shao.OQ4.RademacherS2Assembly.q,
    `Shao.OQ4.RademacherS2Assembly.rho,
    `Shao.OQ4.RademacherS2Assembly.t,
    `Shao.OQ4.RademacherS2Assembly.B.eq_1,
    `Shao.OQ4.RademacherS2Assembly.C_U.eq_1,
    `Shao.OQ4.RademacherS2Assembly.H.eq_1,
    `Shao.OQ4.RademacherS2Assembly.N.eq_1,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_10,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_2,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_4,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_5,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_6,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_7,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_8,
    `Shao.OQ4.RademacherS2Assembly.Q1._simp_1_9,
    `Shao.OQ4.RademacherS2Assembly.R.eq_1,
    `Shao.OQ4.RademacherS2Assembly.a.eq_1,
    `Shao.OQ4.RademacherS2Assembly.eps.eq_1,
    `Shao.OQ4.RademacherS2Assembly.p.eq_1,
    `Shao.OQ4.RademacherS2Assembly.q.eq_1,
    `Shao.OQ4.RademacherS2Assembly.rho.eq_1,
    `Shao.OQ4.RademacherS2Assembly.t.eq_1,
    `Shao.OQ4.RademacherScalarBounds.H.eq_1,
    `Shao.OQ4.RademacherScalarBounds.a.eq_1,
    `Shao.OQ4.RademacherScalarBounds.u.eq_1,
    `Shao.OQ4.RademacherScalarBounds.z.eq_1,
    `Shao.OQ4.RademacherSpectralPairing.amplitude.eq_1]
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
      if owner == `Shao.OQ4.RademacherS2Assembly then
        owned := name :: owned
        if isDefinition then ownedDefinitions := ownedDefinitions + 1
  unless owned.length == expectedOwned.length do throwError "Target actual owner count mismatch"
  for name in expectedOwned do
    unless owned.contains name do throwError "Expected target-owned declaration missing {name}"
  for name in owned do
    unless expectedOwned.contains name do throwError "Unexpected target-owned declaration {name}"
  unless ownedDefinitions == expectedDefinitions.length do throwError "Target definition count mismatch"
  logInfo m!"OQ4_S2_PARENT_PUBLIC_THEOREMS {expectedTheorems.length}"
  logInfo m!"OQ4_S2_PARENT_PUBLIC_DEFINITIONS {expectedDefinitions.length}"
  logInfo m!"OQ4_S2_PARENT_TARGET_OWNED {owned.length}"
  logInfo m!"OQ4_S2_PARENT_PROJECT_RECORDS {count}"
  logInfo m!"OQ4_S2_PARENT_PROJECT_DEFINITIONS {definitionCount}"
  logInfo m!"OQ4_S2_PARENT_TARGET_DEFINITIONS {ownedDefinitions}"
