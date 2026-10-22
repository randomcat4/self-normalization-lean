import Shao.OQ4.RademacherAllModes
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.RademacherAllModes.survivalCoefficient_eq,
    `Shao.OQ4.RademacherAllModes.killedIterKernel_integrable,
    `Shao.OQ4.RademacherAllModes.killedAction_eq_pow,
    `Shao.OQ4.RademacherAllModes.killedIterKernel_integral,
    `Shao.OQ4.RademacherAllModes.killedMass_spectrum,
    `Shao.OQ4.RademacherAllModes.killedIterKernel_real_univ_spectrum,
    `Shao.OQ4.RademacherAllModes.shiftedClosedSurvival_probability_spectrum,
    `Shao.OQ4.RademacherAllModes.closedStrip_probability_spectrum]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf owner then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nOWNER {owner}\nAXIOMS {axioms}"
      count := count + 1
      if owner == `Shao.OQ4.RademacherAllModes then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_ALL_MODES_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_RADEMACHER_ALL_MODES_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_ALL_MODES_AUDITED_CONSTANTS {count}"
