import Shao.OQ3.SymmetricEightAtomSmallPositiveMinimum
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some info := env.find? `Shao.OQ3.exists_symmetric_eight_atom_small_positive_minimum
    | throwError "Missing exact compiled KA theorem"
  let mut todo : List Expr := [info.type]
  let mut instances : Array Expr := #[]
  let mut dataLets : Nat := 0
  while !todo.isEmpty do
    let e := todo.head!
    todo := todo.tail!
    if e.getAppFn.isConstOf `Shao.Probability.bivariateLegendreRate && e.getAppArgs.size == 6 then
      let value := e.getAppArgs[3]!
      if !instances.contains value then instances := instances.push value
    match e with
    | .app f a => todo := f :: a :: todo
    | .lam _ t b _ => todo := t :: b :: todo
    | .forallE _ t b _ => todo := t :: b :: todo
    | .letE _ t v b _ =>
      dataLets := dataLets + 1
      todo := t :: v :: b :: todo
    | .mdata _ b => todo := b :: todo
    | .proj _ _ b => todo := b :: todo
    | _ => pure ()
  unless instances.size > 0 do throwError "No actual hidden rate-instance values found"
  for value in instances do
    logInfo m!"ACTUAL_RATE_NEZERO_RAW {repr value}"
  logInfo m!"KA_STATEMENT_INSTANCE_BINDING PASS\nSOURCE_STATEMENT_LETS 3\nSOURCE_PROOF_LETS 1\nKERNEL_LET_NODES {dataLets}\nDISTINCT_RAW_INSTANCE_VALUES {instances.size}\nOLD_AXIOM_COLLECTIONS 0"
