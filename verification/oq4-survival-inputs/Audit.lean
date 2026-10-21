import Shao.OQ4.IntervalConcentration
import Shao.OQ4.LaplaceTail
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    let owned := match env.getModuleIdxFor? name with
      | some idx => [`Shao.OQ4.IntervalConcentration, `Shao.OQ4.LaplaceTail].contains
          env.header.moduleNames[idx.toNat]!
      | none => false
    if (`Shao.OQ4).isPrefixOf name || owned then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nAXIOMS {axioms}"
      count := count + 1
  logInfo m!"OQ4_SURVIVAL_INPUTS_AUDITED_CONSTANTS {count}"
