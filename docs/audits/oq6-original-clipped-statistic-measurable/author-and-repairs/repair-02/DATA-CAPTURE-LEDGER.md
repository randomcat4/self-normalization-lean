# Unit220 repair02 data and capture ledger

The exact parent-frozen five proof blocks are implemented in the complete source. The public theorem, all 23 typed header values, all seven proof data witnesses/lets and all original assumptions remain unchanged. SOURCE-MAP.json contains their complete types, values, captures and current source ranges. This repair introduces one derived local Prop and no data definition, witness, local instance, premise or global head.

The new local derived Prop `hJfun` appears inside `hJ` at lines 142–148. Its exact type is:

`J = (fun ξ : Fin n → Ω => (∑ i : Fin n, (Shao.OQ6.ResidualDeletion.rowSum (fun j k : Fin n => r (ξ j) (ξ k)) i) ^ 2) / ((n : ℝ) - 2) ^ 2)`.

Its proof value is `funext (fun ξ : Fin n → Ω => residualEnergyJ_eq_rowSqSum n r ξ)`. The source uses a typed `have`, then `funext ξ` and the exact existing theorem. Direct type captures are Ω, n, J and r; direct proof-value captures are Ω, n and r. Transitive original data captures are mΩ, μ, h and g through the frozen definitions. The equality is derived, not an added assumption.

The right-side function expression has type `(Fin n → Ω) → ℝ` and value `fun ξ : Fin n → Ω => (∑ i : Fin n, (Shao.OQ6.ResidualDeletion.rowSum (fun j k : Fin n => r (ξ j) (ξ k)) i) ^ 2) / ((n : ℝ) - 2) ^ 2`. Its direct captures are Ω, n and r. The sample binder ξ has type `Fin n → Ω`; the finite summation index i and matrix indices j, k each have type `Fin n`. The expression is the same pointwise row-square function already present in `hrowsquares` and the existing identity. It is not a new function let or a chosen observation.

The four other repaired blocks add only `Pi.mul_def` and, for the centered row difference, `Pi.sub_def` to `simp only`. Their source invocations add no binder or datum. The pinned definitions express the existing pointwise multiplication/subtraction on real-valued functions over `Fin n → Ω`; actual selected instance values remain subject to the normal server audit. No local instance declaration is added.

The seven unchanged proof data entries, with current source lines, are:

- `F` (line 234): type `({j : Fin n // j ≠ i} → Ω) → ℝ`; value `existential elimination of Shao.OQ6.ResidualDeletion.erasedSamplePairSum_measurable_factorization r hr i`; captures `Ω`, `mΩ`, `n`, `r`, `hr`, `i`.

- `Lrow` (line 242): type `({j : Fin n // j ≠ i} → Ω) → ℝ`; value `existential elimination of Shao.OQ6.ResidualDeletion.erasedSampleRowSqSum_measurable_factorization r hr i`; captures `Ω`, `mΩ`, `n`, `r`, `hr`, `i`.

- `pdel` (line 251): type `(Fin n → Ω) → ({j : Fin n // j ≠ i} → Ω)`; value `fun (ξ : Fin n → Ω) (j : {j : Fin n // j ≠ i}) => ξ j.val`; captures `Ω`, `n`, `i`.

- `Dret` (line 253): type `({j : Fin n // j ≠ i} → Ω) → ℝ`; value `fun q : {j : Fin n // j ≠ i} → Ω => F q / (Real.sqrt (n : ℝ) * ((n : ℝ) - 1))`; captures `Ω`, `n`, `i`, `F`.

- `Jret` (line 256): type `({j : Fin n // j ≠ i} → Ω) → ℝ`; value `fun q : {j : Fin n // j ≠ i} → Ω => Lrow q / ((n : ℝ) - 2) ^ 2`; captures `Ω`, `n`, `i`, `Lrow`.

- `Bret` (line 258): type `({j : Fin n // j ≠ i} → Ω) → ℝ`; value `fun q : {j : Fin n // j ≠ i} → Ω => C0 * (((1 + rho) * 1) / Real.sqrt (n : ℝ) + Jret q / ((1 + rho) * 1 * Real.sqrt (n : ℝ)))`; captures `Ω`, `n`, `i`, `C0`, `rho`, `Jret`.

- `E` (line 262): type `({j : Fin n // j ≠ i} → Ω) → ℝ × ℝ × ℝ`; value `fun q : {j : Fin n // j ≠ i} → Ω => (Dret q, Jret q, Bret q)`; captures `Ω`, `n`, `i`, `Dret`, `Jret`, `Bret`.

The header values remain `g`, `r`, `v`, `rho`, `N`, `W`, `V`, `D`, `J`, `Ddel`, `Jdel`, `A`, `Adel`, `B1`, `B1del`, `s2`, `s`, `d`, `e`, `Tclip`, `Tactual`, `cap`, `deletedTest`. Their types, values and captures are exactly those in the bound prior source map. The old `hpair`, its explicit canonical pair function and all previous parameter/predicate/implicit-structure records remain unchanged; only their current source locations are updated where the seven-line insertion shifts them.

The proof now has 50 named derived Prop proofs, counted from the actual complete source, including the unchanged `hpair` and the added `hJfun`. The source still has one public theorem and seven proof data witnesses/lets. All four unrelated deprecated-if warning sites remain exact. No statement, kernel, projection, residual, original coefficient, guard, cap or retained-subtype construction changes.

Existing classical and canonical real/Pi/product structures are reused. No new local instance is defined or selected as new data. Complete independent affected-proof/interaction review and exact-source server TYPE/VALUE/transitive-axiom evidence remain required. Standard permitted axioms are propext, Classical.choice and Quot.sound; this packet supplies no kernel or axiom-audit result.
