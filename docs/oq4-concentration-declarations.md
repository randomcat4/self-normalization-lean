# IntervalConcentration declaration ledger

Source SHA256: 491e088fccc4457f18701ab7440da8cc9811183d462e3f3b7f22b096ccbf0875.

9 explicit declarations: 1 definition and 8 theorems. The actual import audit selects every declaration owned by Shao.OQ4.IntervalConcentration with getModuleIdxFor? and header.moduleNames, with no namespace or root-name filter. It found 13 total constants, including 4 generated constants. All 13 transitive axiom sets are within {propext, Classical.choice, Quot.sound}.

## Frozen-goal correspondence

- closed_interval_mass_bound_from_cdf: arbitrary Borel probability law, nonnegative L/epsilon, full Lipschitz and actual Iic CDF premises, all a<=b including a=b atoms.
- standardNormalCDF is the actual cdf of gaussianReal 0 1; standardNormalCDF_eq_real identifies its actual Iic real mass.
- standardGaussian_density_le_one and standardGaussian_Ioc_mass_le_length establish the actual Gaussian comparison used by standardNormalCDF_lipschitz (frozen item 2).
- third_absolute_moment_ge_one proves beta>=1 from only genuine square/cube integrability and second moment one (frozen item 3).
- iid_closed_unit_concentration_of_cdf_error proves frozen item 4 on the actual finite product law with t>=1, C_BE>=0, and the explicit actual standardized-sum BE-type CDF error premise. Its internal mapped law and exact closed interval preimage retain every atom.
- real_Ioc_eq_real_Iic_sub is only the half-open interval identity; the closed interval theorem uses a smaller cutoff before a slack limit.

## Explicit declarations

- Shao.OQ4.real_Ioc_eq_real_Iic_sub
- Shao.OQ4.closed_interval_mass_bound_from_cdf
- Shao.OQ4.standardNormalCDF
- Shao.OQ4.standardNormalCDF_eq_real
- Shao.OQ4.standardGaussian_density_le_one
- Shao.OQ4.standardGaussian_Ioc_mass_le_length
- Shao.OQ4.standardNormalCDF_lipschitz
- Shao.OQ4.third_absolute_moment_ge_one
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error

## Generated declarations

- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._proof_1_1
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._simp_1_2
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._simp_1_3
- Shao.OQ4.real_Ioc_eq_real_Iic_sub._simp_1_1

## Complete dynamically enumerated module constants

- Shao.OQ4.closed_interval_mass_bound_from_cdf
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._proof_1_1
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._simp_1_2
- Shao.OQ4.iid_closed_unit_concentration_of_cdf_error._simp_1_3
- Shao.OQ4.real_Ioc_eq_real_Iic_sub
- Shao.OQ4.real_Ioc_eq_real_Iic_sub._simp_1_1
- Shao.OQ4.standardGaussian_Ioc_mass_le_length
- Shao.OQ4.standardGaussian_density_le_one
- Shao.OQ4.standardNormalCDF
- Shao.OQ4.standardNormalCDF_eq_real
- Shao.OQ4.standardNormalCDF_lipschitz
- Shao.OQ4.third_absolute_moment_ge_one

## Curated axiom totals

- 9 constants: propext, Classical.choice, Quot.sound.
- 3 constants: propext.
- 1 constant: propext, Quot.sound.

Original complete logs remain only on the server in repro_outputs/oq4-concentration/. summary.json is a curated hashes/counts/names/axiom-total summary.
