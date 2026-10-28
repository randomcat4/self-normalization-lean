import Shao.OQ6.OriginalLevelDependentCanonicalCoding

set_option autoImplicit false

-- Read exact imported object metadata and definitions; no source proof re-elaboration.
set_option pp.all true in
set_option pp.maxSteps 1000000 in
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let owner := env.getModuleIdxFor? ``Shao.OQ6.OriginalLevelDependentCanonicalCoding.actual_original_level_dependent_canonical_normalized_coding
  unless owner.isSome do
    throwError "Missing imported owned module anchor"
  let allowed := ["propext".toName, "Classical.choice".toName, "Quot.sound".toName]
  let mut count : Nat := 0
  for (name, info) in env.constants.toList do
    if (env.getModuleIdxFor? name) == owner then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless allowed.contains ax do
          throwError "Disallowed owned-module dependency {ax.toString} in {name.toString}"
      let mut parts : List Json := []
      let mut cursor := name
      while cursor != Name.anonymous do
        match cursor with
        | .anonymous => pure ()
        | .str parent segment =>
          parts := Json.mkObj [("kind", Json.str "str"), ("value", Json.str segment)] :: parts
          cursor := parent
        | .num parent number =>
          parts := Json.mkObj [("kind", Json.str "num"), ("value", Json.str (toString number))] :: parts
          cursor := parent
      let bodyValue := info.value? (allowOpaque := true)
      let constantKind := match info with
        | .axiomInfo _ => "axiomInfo"
        | .defnInfo _ => "defnInfo"
        | .thmInfo _ => "thmInfo"
        | .opaqueInfo _ => "opaqueInfo"
        | .quotInfo _ => "quotInfo"
        | .inductInfo _ => "inductInfo"
        | .ctorInfo _ => "ctorInfo"
        | .recInfo _ => "recInfo"
      let entry := Json.mkObj [("components", Json.arr parts.toArray), ("name", Json.str name.toString),
        ("isTheorem", toJson info.isTheorem),
        ("constantKind", Json.str constantKind),
        ("bodyExpressionPresent", toJson bodyValue.isSome),
        ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("axioms", toJson (axioms.toList.map Name.toString))]
      logInfo m!"OQ56_OWNED_JSON {entry.compress}"
      logInfo m!"OQ56_OWNED_TYPE {name.toString} : {info.type}"
      match info with
      | .defnInfo v => logInfo m!"OQ56_OWNED_VALUE {name.toString} := {v.value}"
      | .opaqueInfo _ =>
        if let some value := bodyValue then
          logInfo m!"OQ56_OWNED_VALUE {name.toString} := {value}"
        else
          throwError "Missing required opaque body for {name.toString}"
      | _ => pure ()
      count := count + 1
  unless count ≥ 1 do
    throwError "Incomplete owned-module inventory: {count}"
  logInfo m!"OQ56_OWNED_COUNT {count}"
