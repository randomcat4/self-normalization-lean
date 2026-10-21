import Shao.OQ4.KilledPathLaw
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.measurable_shiftedEndpoint,
    `Shao.OQ4.measurableSet_shiftedClosedSurvival,
    `Shao.OQ4.shiftedClosedSurvival_zero,
    `Shao.OQ4.prefixSum_cons,
    `Shao.OQ4.shiftedEndpoint_cons,
    `Shao.OQ4.shiftedClosedSurvival_cons,
    `Shao.OQ4.path_pi_lintegral_cons,
    `Shao.OQ4.killedKernel_lintegral_shift,
    `Shao.OQ4.killedIterKernel_lintegral_path,
    `Shao.OQ4.killedIterKernel_eq_path_law,
    `Shao.OQ4.killedIterKernel_integral_path,
    `Shao.OQ4.killedMass_eq_path_probability,
    `Shao.OQ4.killedIterKernel_eq_iid_path_law,
    `Shao.OQ4.killedIterKernel_integral_iid_path,
    `Shao.OQ4.killedMass_eq_iid_path_probability,
    `Shao.OQ4.shiftedClosedSurvival_eq_closedStrip,
    `Shao.OQ4.killedMass_eq_closedStrip_probability,
    `Shao.OQ4.killedMass_eq_iid_closedStrip_probability]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]! == `Shao.OQ4.KilledPathLaw
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
      if owned then newCount := newCount + 1
  unless newCount == 35 do
    throwError "Unexpected actual module constant count: {newCount}"
  logInfo m!"OQ4_PATH_LAW_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_PATH_LAW_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_PATH_LAW_AUDITED_CONSTANTS {count}"
