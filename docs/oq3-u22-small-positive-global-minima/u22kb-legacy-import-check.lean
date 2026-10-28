import Shao.OQ3.PhysicalWindowRateFloor
import Shao.OQ3.ActualExteriorFromUniqueMinimum
import Shao.OQ3.BoundedCenteredParabolaSmallPositiveMinimum
import Shao.OQ3.BoundedParabolaLegendreZeroSet
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  for (name, expected) in #[( `Shao.Probability.bivariateLegendreRate.congr_simp,
      `Shao.OQ3.PhysicalWindowRateFloor),
      (`Shao.Probability.bivariateLogMGF.eq_1, `Shao.OQ3.BoundedCenteredParabolaSmallPositiveMinimum),
      (`Shao.Probability.bivariateLogMGF.congr_simp, `Shao.OQ3.BoundedParabolaLegendreZeroSet)] do
    let some info := env.find? name | throwError "Missing generated declaration {name}"
    let some idx := env.getModuleIdxFor? name | throwError "Missing actual owner {name}"
    let owner := env.header.moduleNames[idx.toNat]!
    unless owner == expected do throwError "Unexpected owner {name} {owner}"
    logInfo m!"DECL {name}\nOWNER {owner}\nTYPE {info.type}"
  for name in #[`Shao.OQ3.actual_parabola_rate_floor_of_boundary_lower_bound,
      `Shao.OQ3.actual_exterior_exponential_bound_of_unique_minimum,
      `Shao.OQ3.bounded_centered_parabola_small_positive_global_minimum,
      `Shao.OQ3.bounded_parabola_legendre_zero_and_strictly_positive,
      `Shao.OQ3.bounded_centered_parabola_positive_tail_rate] do
    unless env.contains name do throwError "Missing concrete coimport target {name}"
  logInfo "KB_BY_IV_JZ_COIMPORT PASS\nOLD_AXIOM_COLLECTIONS 0"
