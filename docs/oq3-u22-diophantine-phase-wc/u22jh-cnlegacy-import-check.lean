import Shao.OQ3.CompactOpenDomainAffineFrequencyGap
import Shao.OQ3.SymmetricEightAtomDiophantine
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let name := `Shao.OQ3.jointPhase.eq_1
  let some info := env.find? name | throwError "Missing generated congruence"
  let some idx := env.getModuleIdxFor? name | throwError "Missing actual module owner"
  let owner := env.header.moduleNames[idx.toNat]!
  unless env.contains `Shao.OQ3.symmetric_eight_atom_weak_cramer_of_diophantine_bounds do
    throwError "Missing new Diophantine consumer"
  unless env.contains `Shao.OQ3.compact_open_domain_affine_frequency_gap do
    throwError "Missing accepted old compactgap theorem"
  logInfo m!"JH_CN_COIMPORT PASS\nOWNER {owner}\nTYPE {info.type}\nOLD_AXIOM_COLLECTIONS 0"
