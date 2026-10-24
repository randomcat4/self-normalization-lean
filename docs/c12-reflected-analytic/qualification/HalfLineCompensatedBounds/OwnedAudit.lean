import Shao.C2.HalfLineCompensatedBounds
import Lean

-- The established OwnedAudit selection and collectAxioms gate, restricted to the new owner.
open Lean Elab Command in
set_option pp.all true in
run_cmd do
  let env ← getEnv
  let target := `Shao.C2.HalfLineCompensatedBounds
  let publicNames := #[`Shao.C2.HalfLineCompensatedBounds.upperReflection_small_taylor_bound, `Shao.C2.HalfLineCompensatedBounds.lowerReflection_small_taylor_bound]
  let mut rows : Array Json := #[]
  let mut theoremCount : Nat := 0
  let mut definitionCount : Nat := 0
  let mut publicCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => Name.anonymous
    if owner == target then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed transitive axiom {ax} in {name}"
      let kind := if info matches .thmInfo _ then "theorem"
        else if info matches .defnInfo _ then "definition" else "other"
      rows := rows.push <| Json.mkObj [
        ("name", toJson name.toString), ("owner", toJson owner.toString),
        ("kind", toJson kind), ("axioms", toJson (axioms.map Name.toString))]
      if info matches .thmInfo _ then theoremCount := theoremCount + 1
      if info matches .defnInfo _ then definitionCount := definitionCount + 1
      if publicNames.contains name then
        unless info matches .thmInfo _ do throwError "Expected public theorem {name}"
        publicCount := publicCount + 1
      logInfo m!"TARGET_DECL {name} KIND {kind} AXIOMS {axioms}\nACTUAL_TYPE {info.type}"
      match info with
      | .defnInfo value => logInfo m!"DEFINITION_VALUE {name}\nVALUE {value.value}"
      | _ => pure ()
  unless rows.size > 0 && publicCount == 2 do
    throwError "Incomplete target audit owned={rows.size}, public={publicCount}"
  let report := Json.mkObj [
    ("status", toJson ("PASS" : String)), ("target_module", toJson target.toString),
    ("selection", toJson ("Every target-module-owned constant including private/generated; each collectAxioms result is transitive" : String)),
    ("allowed_axioms", toJson (["propext", "Classical.choice", "Quot.sound"] : List String)),
    ("target_constant_count", toJson rows.size),
    ("target_theorem_count", toJson theoremCount),
    ("target_definition_count_including_private_generated", toJson definitionCount),
    ("public_theorem_count", toJson publicCount), ("module_owned_constants", Json.arr rows)]
  liftIO <| IO.FS.writeFile
    "/root/rivermind-data/shao-lean-20261021/outputs/c12-halfline-compensated-bounds-v71/owned-audit.json"
    (report.pretty ++ "\n")
  logInfo m!"AUDITED_TARGET_CONSTANTS {rows.size} PUBLIC {publicCount} THEOREMS {theoremCount} DEFINITIONS {definitionCount}"

