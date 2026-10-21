import Shao
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expectedText ← liftIO <| IO.FS.readFile "verification/expected-public-theorems.txt"
  let mut expectedCount : Nat := 0
  for line in expectedText.splitOn "
" do
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
  for (name, info) in env.constants.toList do
    if (`Shao).isPrefixOf name && info.isTheorem then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}
TYPE {info.type}
AXIOMS {axioms}"
      elabCommand (← `(#print axioms $(mkIdent name)))
      count := count + 1
  logInfo m!"COVERED_PUBLIC_THEOREMS {expectedCount}"
  logInfo m!"AUDITED_THEOREMS {count}"
