# CosinePowers declaration ledger

Source SHA256: 2f54864af99038bfb3e751d59df9d0f09969ae4aa29cd456c1e0fd8fe6758704.

11 explicit theorems: 4 elementary real scalar helpers and 7 actual-coefficient theorems. Dynamic imported-environment audit found 25 total constants, including 14 generated constants. All transitive axiom sets are subsets of {propext, Classical.choice, Quot.sound}: 13 full-whitelist sets and 12 propext-only sets.

## Actual-coefficient statements and frozen goals

- cosineCoefficient_large_h_remainder: the actual R0 cubic error after beta is bounded by M. This stronger auxiliary bound only needs h >= 1; the final frozen goals retain the full threshold and all moment premises.
- cosineCoefficient_large_h_bounds: item 1, both explicit quadratic bounds and 3/4 <= rho < 1.
- cosineCoefficient_inverse_pow_bound: item 2, every natural n including zero.
- cosineCoefficient_inverse_pow_uniform: item 2 under (n : real) <= 2 h^2.
- cosineCoefficient_floor_inverse_bounds: item 2, both floor(h^2)+1 and 2 floor(h^2).
- cosineCoefficient_log_error: item 3, exact displayed M-dependent constant.
- cosineCoefficient_log_error_mul: item 3, exact N-multiple including zero.

Every final frozen-goal theorem uses the actual cosineCoefficient nu (pi / (2*h)) and retains genuine integrability of id, square and absolute cube, mean zero, second moment one, M >= 0, beta <= M, h >= 1 and pi(1+M) <= h.

## Explicit declarations

- Shao.OQ4.cosine_powers_scalar_bounds
- Shao.OQ4.cosine_powers_inverse_scalar
- Shao.OQ4.cosine_powers_log_linear_scalar
- Shao.OQ4.cosine_powers_log_error_scalar
- Shao.OQ4.cosineCoefficient_large_h_remainder
- Shao.OQ4.cosineCoefficient_large_h_bounds
- Shao.OQ4.cosineCoefficient_inverse_pow_bound
- Shao.OQ4.cosineCoefficient_inverse_pow_uniform
- Shao.OQ4.cosineCoefficient_floor_inverse_bounds
- Shao.OQ4.cosineCoefficient_log_error
- Shao.OQ4.cosineCoefficient_log_error_mul

## Generated declarations

- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_1
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_2
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_3
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_4
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_5
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_6
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_7
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_1
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_2
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_3
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_4
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_5
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_6
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_7

## All dynamically enumerated constants

- Shao.OQ4.cosineCoefficient_floor_inverse_bounds
- Shao.OQ4.cosineCoefficient_inverse_pow_bound
- Shao.OQ4.cosineCoefficient_inverse_pow_uniform
- Shao.OQ4.cosineCoefficient_large_h_bounds
- Shao.OQ4.cosineCoefficient_large_h_remainder
- Shao.OQ4.cosineCoefficient_log_error
- Shao.OQ4.cosineCoefficient_log_error_mul
- Shao.OQ4.cosine_powers_inverse_scalar
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_1
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_2
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_3
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_4
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_5
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_6
- Shao.OQ4.cosine_powers_inverse_scalar._simp_1_7
- Shao.OQ4.cosine_powers_log_error_scalar
- Shao.OQ4.cosine_powers_log_linear_scalar
- Shao.OQ4.cosine_powers_scalar_bounds
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_1
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_2
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_3
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_4
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_5
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_6
- Shao.OQ4.cosine_powers_scalar_bounds._simp_1_7

Full original audit output stays on the server in repro_outputs/oq4-powers/audit.log. summary.json contains only curated hashes, counts, names, and axiom-set totals.
