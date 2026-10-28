import Shao.OQ3.PhysicalWindowRateFloor
import Shao.OQ3.ActualExteriorFromUniqueMinimum
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := `Shao.Probability.bivariateLegendreRate.congr_simp
  let some info := env.find? name | throwError "Missing generated congruence"
  let some idx := env.getModuleIdxFor? name | throwError "Missing actual module owner"
  let owner := env.header.moduleNames[idx.toNat]!
  let axioms ← Lean.collectAxioms name
  for ax in axioms do
    unless [`propext, `Classical.choice, `Quot.sound].contains ax do
      throwError "Disallowed axiom {ax}"
  unless env.contains `Shao.OQ3.actual_exterior_exponential_bound_of_unique_minimum do
    throwError "Missing new exterior theorem"
  unless env.contains `Shao.OQ3.actual_parabola_rate_floor_of_boundary_lower_bound do
    throwError "Missing accepted old floor theorem"
  logInfo m!"IV_BY_COIMPORT PASS\nOWNER {owner}\nTYPE {info.type}\nAXIOMS {axioms}"
