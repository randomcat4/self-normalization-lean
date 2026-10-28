import Shao.OQ6.OriginalSameWitnessClippedTailApplication

set_option autoImplicit false

-- Import-only TYPE supplement; the accepted source and its first object stay unchanged.
set_option pp.all true in
set_option pp.maxSteps 1000000 in
set_option maxRecDepth 8192 in
open Lean Elab Command in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let anchor := ``Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application
    let owner := env.getModuleIdxFor? anchor
    unless owner.isSome do
      throwError "Missing imported module anchor"
    let targets := [
      "Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application._proof_1_1".toName,
      "Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application._proof_1_2".toName]
    for name in targets do
      unless env.getModuleIdxFor? name == owner do
        throwError "Target does not have the exact imported module owner: {name.toString}"
      let info ← getConstInfo name
      unless info.isTheorem && (info.value? (allowOpaque := true)).isSome do
        throwError "Expected original generated theorem with its body: {name.toString}"
      let (representation, text) ←
        try
          let fmt ← PrettyPrinter.ppExpr info.type
          pure ("full-pretty-printed-Expr", fmt.pretty)
        catch _ =>
          pure ("derived-Repr-complete-Expr", reprStr info.type)
      let entry := Json.mkObj [
        ("name", Json.str name.toString),
        ("levelParams", toJson (info.levelParams.map Name.toString)),
        ("representation", Json.str representation),
        ("type", Json.str text)]
      logInfo m!"OQ56_HELPER_TYPE_JSON {entry.compress}"
    logInfo m!"OQ56_HELPER_TYPE_COUNT 2"
