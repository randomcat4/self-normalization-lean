import Shao.OQ3.SelfNormalizedLowEnergyExponentialBound
import Lean

set_option pp.deepTerms true
set_option pp.maxSteps 1000000

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let targets : Array Name := #[`Shao.OQ3.exists_self_normalized_low_energy_arbitrary_exponential_bound]
  let defs : Array Name := #[]
  for name in targets do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Expected theorem {name}"
    | none => throwError "Missing frozen theorem {name}"
  for name in defs do
    match env.find? name with
    | some (.defnInfo _) => pure ()
    | _ => throwError "Missing frozen definition {name}"
  let mut allCount : Nat := 0
  let mut theoremCount : Nat := 0
  let mut targetCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if owner == `Shao.OQ3.SelfNormalizedLowEnergyExponentialBound then
      if info.isAxiom then throwError "New project axiom {name}"
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      if info.isTheorem then logInfo "KIND theorem"
      match info with
      | .defnInfo d =>
        unless d.safety == .safe do throwError "Non-safe definition {name}"
        logInfo m!"SAFETY {repr d.safety}\nVALUE {d.value}"
      | _ => pure ()
      allCount := allCount + 1
      if info.isTheorem then theoremCount := theoremCount + 1
      if targets.contains name then targetCount := targetCount + 1
  unless allCount > 0 do throwError "Empty actual module ownership audit"
  unless targetCount == 1 do throwError "Frozen count mismatch {targetCount}"
  logInfo m!"U22IN_FROZEN_DEFINITIONS {defs.size}"
  logInfo m!"U22IN_FROZEN_THEOREMS {targetCount}"
  logInfo m!"U22IN_ALL_THEOREMS {theoremCount}"
  logInfo m!"U22IN_ALL_DECLARATIONS {allCount}"
  logInfo m!"U22IN_AXIOM_GATE PASS"
