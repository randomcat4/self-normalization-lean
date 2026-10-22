import Shao.OQ4.RademacherSpectralTail
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedTheorems : List Name := [
    `Shao.OQ4.RademacherSpectralTail.decayRatio_pos,
    `Shao.OQ4.RademacherSpectralTail.decayRatio_lt_one,
    `Shao.OQ4.RademacherSpectralTail.absoluteC_pos,
    `Shao.OQ4.RademacherSpectralTail.remainder_uniform,
    `Shao.OQ4.RademacherSpectralTail.remainder_uniform_weakCell,
    `Shao.OQ4.RademacherSpectralTail.exists_absolute_uniform_remainder_bound,
    `Shao.OQ4.RademacherSpectralTail.remainder_one_positive_time,
    `Shao.OQ4.RademacherSpectralTail.remainder_two_positive_time]
  let expectedDefinitions : List Name := [
    `Shao.OQ4.RademacherSpectralTail.decayRatio,
    `Shao.OQ4.RademacherSpectralTail.absoluteC]
  for name in expectedTheorems do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  for name in expectedDefinitions do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing public definition: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  let mut definitions : Nat := 0
  let mut newDefinitions : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao).isPrefixOf owner || (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf (privateToUserName name) then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nOWNER {owner}\nAXIOMS {axioms}"
      count := count + 1
      let isDefinition := match info with | .defnInfo _ => true | _ => false
      if isDefinition then definitions := definitions + 1
      if owner == `Shao.OQ4.RademacherSpectralTail then
        newCount := newCount + 1
        if isDefinition then newDefinitions := newDefinitions + 1
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_TAIL_PUBLIC_THEOREMS {expectedTheorems.length}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_TAIL_PUBLIC_DEFINITIONS {expectedDefinitions.length}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_TAIL_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_TAIL_AUDITED_CONSTANTS {count}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_TAIL_DEFINITIONS {definitions}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_TAIL_NEW_DEFINITIONS {newDefinitions}"
