import Shao.OQ4.RademacherSpectralPairing
import Lean

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let expected : List Name := [
    `Shao.OQ4.RademacherSpectralPairing.mem_lowerModes,
    `Shao.OQ4.RademacherSpectralPairing.lowerModes_le,
    `Shao.OQ4.RademacherSpectralPairing.reflect_involutive,
    `Shao.OQ4.RademacherSpectralPairing.reflect_injective_on,
    `Shao.OQ4.RademacherSpectralPairing.mem_reflectedModes,
    `Shao.OQ4.RademacherSpectralPairing.mem_centerModes,
    `Shao.OQ4.RademacherSpectralPairing.even_twice_half,
    `Shao.OQ4.RademacherSpectralPairing.centerModes_eq,
    `Shao.OQ4.RademacherSpectralPairing.lower_reflected_disjoint,
    `Shao.OQ4.RademacherSpectralPairing.paired_center_disjoint,
    `Shao.OQ4.RademacherSpectralPairing.range_partition,
    `Shao.OQ4.RademacherSpectralPairing.sum_reflection_partition,
    `Shao.OQ4.RademacherSpectralPairing.lower_frequency,
    `Shao.OQ4.RademacherSpectralPairing.reflected_frequency,
    `Shao.OQ4.RademacherSpectralPairing.alpha_reflect,
    `Shao.OQ4.RademacherSpectralPairing.beta_reflect,
    `Shao.OQ4.RademacherSpectralPairing.beta_eq_twice_alpha,
    `Shao.OQ4.RademacherSpectralPairing.alpha_bounds,
    `Shao.OQ4.RademacherSpectralPairing.sin_alpha_pos,
    `Shao.OQ4.RademacherSpectralPairing.beta_bounds,
    `Shao.OQ4.RademacherSpectralPairing.beta_strict_mono,
    `Shao.OQ4.RademacherSpectralPairing.lower_alpha_bounds,
    `Shao.OQ4.RademacherSpectralPairing.lower_beta_bounds,
    `Shao.OQ4.RademacherSpectralPairing.lower_trig_denominators,
    `Shao.OQ4.RademacherSpectralPairing.cos_beta_pos,
    `Shao.OQ4.RademacherSpectralPairing.cotangent_reflect,
    `Shao.OQ4.RademacherSpectralPairing.cos_beta_reflect,
    `Shao.OQ4.RademacherSpectralPairing.cos_beta_neg,
    `Shao.OQ4.RademacherSpectralPairing.eigenvalue_le_rho,
    `Shao.OQ4.RademacherSpectralPairing.neg_rho_le_eigenvalue,
    `Shao.OQ4.RademacherSpectralPairing.alpha_center,
    `Shao.OQ4.RademacherSpectralPairing.beta_center,
    `Shao.OQ4.RademacherSpectralPairing.cotangent_pi_div_four,
    `Shao.OQ4.RademacherSpectralPairing.cos_beta_zero_iff,
    `Shao.OQ4.RademacherSpectralPairing.zero_mem_lowerModes,
    `Shao.OQ4.RademacherSpectralPairing.amplitude_pos,
    `Shao.OQ4.RademacherSpectralPairing.rho_pos,
    `Shao.OQ4.RademacherSpectralPairing.rho_lt_one,
    `Shao.OQ4.RademacherSpectralPairing.normalizer_pos,
    `Shao.OQ4.RademacherSpectralPairing.principal_cotangent_pos,
    `Shao.OQ4.RademacherSpectralPairing.sign_reflect,
    `Shao.OQ4.RademacherSpectralPairing.pair_term,
    `Shao.OQ4.RademacherSpectralPairing.full_sum_pairing,
    `Shao.OQ4.RademacherSpectralPairing.raw_spectral_pairing,
    `Shao.OQ4.RademacherSpectralPairing.killedMass_paired,
    `Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_paired,
    `Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_eq_killedMass,
    `Shao.OQ4.RademacherSpectralPairing.last_mode_coefficient,
    `Shao.OQ4.RademacherSpectralPairing.last_mode_eigenvalue,
    `Shao.OQ4.RademacherSpectralPairing.last_mode_contribution,
    `Shao.OQ4.RademacherSpectralPairing.first_pair,
    `Shao.OQ4.RademacherSpectralPairing.normalized_term,
    `Shao.OQ4.RademacherSpectralPairing.paired_sum_normalized,
    `Shao.OQ4.RademacherSpectralPairing.killedMass_normalized,
    `Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_normalized,
    `Shao.OQ4.RademacherSpectralPairing.zeroMode_positive_time,
    `Shao.OQ4.RademacherSpectralPairing.zeroMode_zero,
    `Shao.OQ4.RademacherSpectralPairing.remainder_positive_time,
    `Shao.OQ4.RademacherSpectralPairing.remainder_frequency,
    `Shao.OQ4.RademacherSpectralPairing.normalized_zero,
    `Shao.OQ4.RademacherSpectralPairing.closedStrip_probability_zero,
    `Shao.OQ4.RademacherSpectralPairing.lowerModes_one,
    `Shao.OQ4.RademacherSpectralPairing.lowerModes_two,
    `Shao.OQ4.RademacherSpectralPairing.tail_one_empty,
    `Shao.OQ4.RademacherSpectralPairing.tail_two_empty,
    `Shao.OQ4.RademacherSpectralPairing.remainder_one,
    `Shao.OQ4.RademacherSpectralPairing.remainder_two_positive_time,
    `Shao.OQ4.RademacherSpectralPairing.zeroMode_two_zero,
    `Shao.OQ4.RademacherSpectralPairing.remainder_two_zero]
  for name in expected do
    match env.find? name with
    | some info => unless info.isTheorem do throwError "Not a theorem: {name}"
    | none => throwError "Missing public theorem: {name}"
  let mut count : Nat := 0
  let mut newCount : Nat := 0
  for (name, info) in env.constants.toList do
    let owner := match env.getModuleIdxFor? name with
      | some idx => env.header.moduleNames[idx.toNat]!
      | none => .anonymous
    if (`Shao.OQ4).isPrefixOf name || (`Shao.OQ4).isPrefixOf owner then
      let axioms ← Lean.collectAxioms name
      for ax in axioms do
        unless [`propext, `Classical.choice, `Quot.sound].contains ax do
          throwError "Disallowed axiom {ax} in {name}"
      logInfo m!"DECL {name}\nTYPE {info.type}\nOWNER {owner}\nAXIOMS {axioms}"
      count := count + 1
      if owner == `Shao.OQ4.RademacherSpectralPairing then newCount := newCount + 1
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_PAIRING_PUBLIC_THEOREMS {expected.length}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_PAIRING_NEW_CONSTANTS {newCount}"
  logInfo m!"OQ4_RADEMACHER_SPECTRAL_PAIRING_AUDITED_CONSTANTS {count}"
