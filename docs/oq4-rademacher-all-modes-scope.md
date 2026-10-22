# Actual all-mode finite powers and constant-one survival spectrum

STATUS: LEAN_FULLY_CHECKED_ALL_MODES_D1_D2_CONSTANT_ONE
SPECTRUM_STATUS: OPEN
OQ4_ROOT_STATUS: OPEN
MAIN_INTEGRATION_STATUS: PENDING_ROOT

For every m>=1, m<=h<m+1, integer r in [-m,m], mode j in [1,2m+1], and natural n including zero, the actual iterated killed kernel of the fixed half-Dirac Rademacher law genuinely integrates the sine mode and gives cos(j*pi/(2*(m+1)))^n times its value at r. The proof uses the actual integer-grid support and actual kernel semigroup. Zero and negative eigenvalues remain in range and no division by a mode or survival mass occurs.

For constant-one data only, the actual killedMass and actual real total mass equal the finite sum q_j*mu_j^n*v_j(r), with q_j=(1/(m+1))*sum_s v_j(s) under the original counting normalization. The same identity is bridged to the actual shifted path probability; at zero it is the actual product-law closedStrip probability, using its required nonnegative-threshold condition. The finite reconstruction is used only almost everywhere on the actual grid, not asserted to equal one off the grid.

Eight explicit public theorems, one public definition, four private theorems and four generated theorems give seventeen source/direct-target owned constants. Three generated names outside the target namespace are included. In all41 imports, Shao.OQ4.killedAction.congr_simp is already present under its old owner with identical audited fields; the union therefore adds sixteen distinct constants and totals863. No declaration is filtered out. There are no new instances. Independent source semantics, anonymous mathematics, final direct no-o/full original-source/actual-import checks and lead import-only audits are required by the receipts. Only propext, Classical.choice and Quot.sound occur; raw Expr/logs/binaries stay server-only.

This closes D1 and D2 for constant-one data only. Cot coefficients, the explicit zero-start S1, low thresholds, S2-S5 asymptotics, strict events, other cosets, full atomic/general-data spectra and the OQ4 root remain OPEN. The source-semantic review discloses limited old accepted helper-proof exposure; it did not read the new implementation or anonymous proof. The final formal review separately records accidental visibility of two old first-mode helper proof bodies, and checks the general-mode and constant-one conclusions independently of those helpers. No common/root/import/pin/cache edits are included; main integration belongs to the root coordinator.
