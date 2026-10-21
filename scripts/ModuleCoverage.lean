import Shao
import Lean
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected ← liftIO <| IO.FS.readFile "verification/expected-project-modules.txt"
  let mut count : Nat := 0
  for line in expected.splitOn "\n" do
    let label := line.trimAscii.toString
    unless label.isEmpty do
      unless env.header.moduleNames.contains label.toName do
        throwError "Missing project module: {label}"
      count := count + 1
  unless count > 0 do
    throwError "Empty project module list"
  logInfo m!"COVERED_PROJECT_MODULES {count}"
