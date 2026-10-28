import Shao.OQ6.OriginalSameWitnessClippedTailApplication

set_option autoImplicit false

open Lean Elab Command Meta

namespace OQ56HelperTypeObservation246

private structure Encoded where
  ids : ExprStructMap Nat := {}
  nodes : Array Json := #[]

private def nameData (n : Name) : Json := Id.run do
  let mut parts : List Json := []
  let mut cursor := n
  while cursor != Name.anonymous do
    match cursor with
    | .anonymous => pure ()
    | .str parent segment =>
      parts := Json.mkObj [("kind", Json.str "str"), ("value", Json.str segment)] :: parts
      cursor := parent
    | .num parent number =>
      parts := Json.mkObj [("kind", Json.str "num"), ("value", toJson number)] :: parts
      cursor := parent
  return Json.arr parts.toArray

private def visit : Nat → Expr → StateT Encoded MetaM Nat
  | 0, _ => throwError "TYPE expression traversal depth exhausted; no complete evidence"
  | fuel + 1, e => do
    if let some id := (← get).ids.get? ⟨e⟩ then
      return id
    let fields ← match e with
      | .bvar i => pure [("tag", Json.str "bvar"), ("index", toJson i)]
      | .fvar id => pure [("tag", Json.str "fvar"), ("name", nameData id.name)]
      | .mvar id => pure [("tag", Json.str "mvar"), ("name", nameData id.name)]
      | .sort u => pure [("tag", Json.str "sort"), ("levelRepr", Json.str (reprStr u))]
      | .const n us =>
        pure [("tag", Json.str "const"), ("name", nameData n),
          ("levelReprs", toJson (us.map reprStr))]
      | .app f a => do
        let fId ← visit fuel f
        let aId ← visit fuel a
        pure [("tag", Json.str "app"), ("function", toJson fId), ("argument", toJson aId)]
      | .lam n d b bi => do
        let dId ← visit fuel d
        let bId ← visit fuel b
        pure [("tag", Json.str "lam"), ("name", nameData n),
          ("binderInfoRepr", Json.str (reprStr bi)), ("domain", toJson dId), ("body", toJson bId)]
      | .forallE n d b bi => do
        let dId ← visit fuel d
        let bId ← visit fuel b
        pure [("tag", Json.str "forallE"), ("name", nameData n),
          ("binderInfoRepr", Json.str (reprStr bi)), ("domain", toJson dId), ("body", toJson bId)]
      | .letE n t v b nd => do
        let tId ← visit fuel t
        let vId ← visit fuel v
        let bId ← visit fuel b
        pure [("tag", Json.str "letE"), ("name", nameData n), ("type", toJson tId),
          ("value", toJson vId), ("body", toJson bId), ("nondep", toJson nd)]
      | .lit v => pure [("tag", Json.str "lit"), ("literalRepr", Json.str (reprStr v))]
      | .mdata d b => do
        let bId ← visit fuel b
        pure [("tag", Json.str "mdata"), ("metadataRepr", Json.str (reprStr d)), ("body", toJson bId)]
      | .proj n i b => do
        let bId ← visit fuel b
        pure [("tag", Json.str "proj"), ("name", nameData n), ("index", toJson i), ("body", toJson bId)]
    let st ← get
    let id := st.nodes.size
    set ({ ids := st.ids.insert ⟨e⟩ id, nodes := st.nodes.push (Json.mkObj (("id", toJson id) :: fields)) } : Encoded)
    return id

set_option maxRecDepth 8192 in
run_cmd do
  liftTermElabM do
    let env ← getEnv
    let owner := env.getModuleIdxFor? ``Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application
    unless owner.isSome do
      throwError "Missing original imported module anchor"
    let targets := [
      "Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application._proof_1_1".toName,
      "Shao.OQ6.OriginalSameWitnessClippedTailApplication.actual_original_same_witness_clipped_scalar_tail_application._proof_1_2".toName]
    let mut encoded : Encoded := {}
    let mut roots : Array Json := #[]
    for name in targets do
      unless env.getModuleIdxFor? name == owner do
        throwError "Target module owner mismatch: {name.toString}"
      let info ← getConstInfo name
      unless info.isTheorem && (info.value? (allowOpaque := true)).isSome do
        throwError "Target is not original generated theorem with body: {name.toString}"
      unless !info.type.hasFVar && !info.type.hasExprMVar && !info.type.hasLevelMVar do
        throwError "Imported TYPE unexpectedly has an open variable: {name.toString}"
      let (root, next) ← (visit 16384 info.type).run encoded
      encoded := next
      roots := roots.push (Json.mkObj [("name", Json.str name.toString),
        ("nameComponents", nameData name), ("levelParams", toJson (info.levelParams.map nameData)),
        ("root", toJson root)])
    let packet := Json.mkObj [("schema", Json.str "exact-ExprStructEq-DAG-v1"),
      ("roots", Json.arr roots), ("nodes", Json.arr encoded.nodes),
      ("nodeCount", toJson encoded.nodes.size), ("helperCount", toJson roots.size)]
    logInfo m!"OQ56_HELPER_TYPE_DAG_JSON {packet.compress}"
    logInfo m!"OQ56_HELPER_TYPE_COUNT 2"

end OQ56HelperTypeObservation246
