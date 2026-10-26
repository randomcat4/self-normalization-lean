import Shao
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedText ← liftIO <| IO.FS.readFile "verification/expected-public-theorems.txt"
  let selectedText ← liftIO <| IO.FS.readFile "verification/integration-audit-modules.txt"
  let selected := (selectedText.splitOn "\n").map (fun s => s.trimAscii.toString.toName)
  let mut expectedCount : Nat := 0
  for line in expectedText.splitOn "\n" do
    let label := line.trimAscii.toString
    unless label.isEmpty do
      let name := label.toName
      match env.find? name with
      | some info =>
        unless info.isTheorem && (`Shao).isPrefixOf name do
          throwError "Manifest entry is not a project theorem: {name}"
      | none => throwError "Public source theorem missing from imported library: {name}"
      expectedCount := expectedCount + 1
  unless expectedCount > 0 do
    throwError "Empty public theorem manifest"
  let mut count : Nat := 0
  let mut checked : Nat := 0
  for (name, info) in env.constants.toList do
    if (`Shao).isPrefixOf name && info.isTheorem then
      let affected := match env.getModuleIdxFor? name with
        | some idx => selected.contains env.header.moduleNames[idx.toNat]!
        | none => false
      logInfo m!"DECL {name}"
      if affected then
        let axioms ← Lean.collectAxioms name
        for ax in axioms do
          unless [`propext, `Classical.choice, `Quot.sound].contains ax do
            throwError "Disallowed axiom {ax} in {name}"
        logInfo m!"TYPE {info.type}\nAXIOMS {axioms}\nAXIOM_CHECKED_THEOREM {name}"
        checked := checked + 1
      count := count + 1
  logInfo m!"COVERED_PUBLIC_THEOREMS {expectedCount}"
  logInfo m!"AUDITED_THEOREMS {count}"
  logInfo m!"AXIOM_CHECKED_THEOREMS {checked}"
