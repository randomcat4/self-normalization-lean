# KilledPathLaw declaration ledger

Source SHA256: 1f1b664d81e551bb6a58ca335c3b568cfbd684e991e12b733f599a5ed2eada9f.

20 explicit declarations: 2 definitions and 18 theorems. Actual imported-environment audit selected every declaration owned by Shao.OQ4.KilledPathLaw using getModuleIdxFor? and header.moduleNames, without namespace or name-prefix filtering. It found 35 total new constants, including 15 generated constants. All 35 transitive axiom sets are within {propext, Classical.choice, Quot.sound}.

## Frozen-goal correspondence

- Item 1: shiftedClosedSurvival, shiftedEndpoint, their measurability results, killedIterKernel_lintegral_path, and killedIterKernel_eq_path_law. The law is exact for every n,h,z.
- Item 2: killedIterKernel_integral_path records actual integrability of both sides and equality; killedMass_eq_path_probability is the real survival-mass identity.
- Item 3: killedIterKernel_eq_iid_path_law, killedIterKernel_integral_iid_path, and killedMass_eq_iid_path_probability use the shared FiniteIID joint-law theorem.
- Item 4: shiftedClosedSurvival_eq_closedStrip is a pointwise set identity when h>=0; killedMass_eq_closedStrip_probability and killedMass_eq_iid_closedStrip_probability provide both probability interfaces.
- The remaining helpers establish empty-time survival, exact cons prefix/endpoint/event identities, first-coordinate product splitting, and the unnormalized one-step nonnegative integral formula.

## Explicit declarations

- Shao.OQ4.shiftedClosedSurvival
- Shao.OQ4.shiftedEndpoint
- Shao.OQ4.measurable_shiftedEndpoint
- Shao.OQ4.measurableSet_shiftedClosedSurvival
- Shao.OQ4.shiftedClosedSurvival_zero
- Shao.OQ4.prefixSum_cons
- Shao.OQ4.shiftedEndpoint_cons
- Shao.OQ4.shiftedClosedSurvival_cons
- Shao.OQ4.path_pi_lintegral_cons
- Shao.OQ4.killedKernel_lintegral_shift
- Shao.OQ4.killedIterKernel_lintegral_path
- Shao.OQ4.killedIterKernel_eq_path_law
- Shao.OQ4.killedIterKernel_integral_path
- Shao.OQ4.killedMass_eq_path_probability
- Shao.OQ4.killedIterKernel_eq_iid_path_law
- Shao.OQ4.killedIterKernel_integral_iid_path
- Shao.OQ4.killedMass_eq_iid_path_probability
- Shao.OQ4.shiftedClosedSurvival_eq_closedStrip
- Shao.OQ4.killedMass_eq_closedStrip_probability
- Shao.OQ4.killedMass_eq_iid_closedStrip_probability

## Generated declarations

- Shao.OQ4.killedIterKernel_lintegral_path._simp_1_2
- Shao.OQ4.killedKernel_lintegral_shift._simp_1_1
- Shao.OQ4.killedKernel_lintegral_shift._simp_1_2
- Shao.OQ4.shiftedClosedSurvival.eq_1
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_1
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_2
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_3
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_4
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_5
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_6
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_7
- Shao.OQ4.shiftedClosedSurvival_eq_closedStrip._proof_1_1
- Shao.OQ4.shiftedClosedSurvival_zero._proof_1_3
- Shao.OQ4.shiftedClosedSurvival_zero._simp_1_2
- Shao.OQ4.shiftedEndpoint.eq_1

## Complete dynamically enumerated module constants

- Shao.OQ4.killedIterKernel_eq_iid_path_law
- Shao.OQ4.killedIterKernel_eq_path_law
- Shao.OQ4.killedIterKernel_integral_iid_path
- Shao.OQ4.killedIterKernel_integral_path
- Shao.OQ4.killedIterKernel_lintegral_path
- Shao.OQ4.killedIterKernel_lintegral_path._simp_1_2
- Shao.OQ4.killedKernel_lintegral_shift
- Shao.OQ4.killedKernel_lintegral_shift._simp_1_1
- Shao.OQ4.killedKernel_lintegral_shift._simp_1_2
- Shao.OQ4.killedMass_eq_closedStrip_probability
- Shao.OQ4.killedMass_eq_iid_closedStrip_probability
- Shao.OQ4.killedMass_eq_iid_path_probability
- Shao.OQ4.killedMass_eq_path_probability
- Shao.OQ4.measurableSet_shiftedClosedSurvival
- Shao.OQ4.measurable_shiftedEndpoint
- Shao.OQ4.path_pi_lintegral_cons
- Shao.OQ4.prefixSum_cons
- Shao.OQ4.shiftedClosedSurvival
- Shao.OQ4.shiftedClosedSurvival.eq_1
- Shao.OQ4.shiftedClosedSurvival_cons
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_1
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_2
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_3
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_4
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_5
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_6
- Shao.OQ4.shiftedClosedSurvival_cons._proof_1_7
- Shao.OQ4.shiftedClosedSurvival_eq_closedStrip
- Shao.OQ4.shiftedClosedSurvival_eq_closedStrip._proof_1_1
- Shao.OQ4.shiftedClosedSurvival_zero
- Shao.OQ4.shiftedClosedSurvival_zero._proof_1_3
- Shao.OQ4.shiftedClosedSurvival_zero._simp_1_2
- Shao.OQ4.shiftedEndpoint
- Shao.OQ4.shiftedEndpoint.eq_1
- Shao.OQ4.shiftedEndpoint_cons

## Curated axiom totals

- 23 constants: propext, Classical.choice, Quot.sound.
- 10 constants: propext, Quot.sound.
- 2 constants: propext.

The complete original audit log remains only on the server in repro_outputs/oq4-path-law/audit.log. summary.json contains only curated hashes, counts, names, and axiom-set totals.
