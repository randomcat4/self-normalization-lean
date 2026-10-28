import Shao.OQ3.PhysicalWindowRateFloor
import Shao.OQ3.ActualExteriorFromUniqueMinimum
import Shao.OQ3.BoundedCenteredParabolaSmallPositiveMinimum
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := `Shao.Probability.bivariateLegendreRate.congr_simp
  let some info := env.find? name | throwError "Missing generated congruence"
  let some idx := env.getModuleIdxFor? name | throwError "Missing actual module owner"
  let owner := env.header.moduleNames[idx.toNat]!
  unless owner == `Shao.OQ3.PhysicalWindowRateFloor do
    throwError "Unexpected known generated owner {owner}"
  for target in #[`Shao.OQ3.actual_parabola_rate_floor_of_boundary_lower_bound,
      `Shao.OQ3.actual_exterior_exponential_bound_of_unique_minimum,
      `Shao.OQ3.bounded_centered_parabola_small_positive_global_minimum] do
    unless env.contains target do throwError "Missing concrete co-import target {target}"
  logInfo m!"JZ_BY_IV_COIMPORT PASS\nOWNER {owner}\nTYPE {info.type}\nOLD_AXIOM_COLLECTIONS 0"
