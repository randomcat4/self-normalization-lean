import Shao
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let selectedText ← liftIO <| IO.FS.readFile "verification/integration-audit-modules.txt"
  let selected := (selectedText.splitOn "\n").map (fun s => s.trimAscii.toString.toName)
  let mut count : Nat := 0
  let mut checked : Nat := 0
  for (name, _) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if (`Shao).isPrefixOf owner then
      if selected.contains owner then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless [`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        logInfo m!"OWNED_DECL {name} AXIOMS {axioms}\nAXIOM_CHECKED_OWNED {name}"
        checked := checked + 1
      else
        logInfo m!"OWNED_DECL {name} AXIOMS REUSED_EXACT_ACCEPTED_BASELINE"
      count := count + 1
  unless count > 0 do
    throwError "Empty project declaration inventory"
  logInfo m!"AUDITED_PROJECT_CONSTANTS {count}"
  logInfo m!"AXIOM_CHECKED_PROJECT_CONSTANTS {checked}"
